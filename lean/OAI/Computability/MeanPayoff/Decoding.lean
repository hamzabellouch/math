import OAI.Computability.MeanPayoff.BitDepth

namespace OAI

section

namespace MeanPayoff

def nodeRandomBound (n Bmax : ℕ) : ℕ :=
  globalJ n Bmax * ((globalG Bmax + 1) * sampleExponent Bmax)

theorem SolveBox.resource_repeated {n Bmax : ℕ} (I : SolveBox n Bmax)
    {t : Counted (BoxVector I)} {K : ℕ} (h : t.Resource K 0) (J : ℕ) :
    (I.repeatedCounted t J).Resource K 0 := by
  simpa only [SolveBox.repeatedCounted, Nat.mul_zero] using Counted.resource_map I.medianBox (Counted.resource_trials h J)

namespace CountedAlgorithm

def LowerResource {n Bmax : ℕ} {P : Budgets n} (lower : LowerSolver (Bmax := Bmax) P)
    (K : ℕ) : Prop := ∀ Q h I, (lower Q h I).Resource K 0

theorem resource_centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {K : ℕ} (hK : LowerResource lower K)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (centerUpdate P hR lower I hB q).Resource K 0 := by
  unfold centerUpdate
  exact Counted.resource_bind _
    (SolveBox.resource_repeated _ (hK _ _ _) _)
    (fun _ => Counted.resource_map _ (SolveBox.resource_repeated _ (hK _ _ _) _))

theorem resource_centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {K : ℕ} (hK : LowerResource lower K)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).Resource K 0 := by
  induction t generalizing q with
  | zero => exact Counted.resource_pure _ _ _
  | succ t ih =>
    exact Counted.resource_bind _ (F := 0) (resource_centerUpdate P hR lower hK I hB q)
      (fun q' => Counted.resource_map _ (ih q'))

theorem resource_orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → Counted (Orientation P)) {K E : ℕ}
    (h : ∀ q, (child q).Resource K E) :
    (orientationTail G P I qs child).Resource K (sampleExponent Bmax + E) := by
  unfold orientationTail
  dsimp only
  split_ifs
  · exact Counted.resource_pure _ _ _
  · exact Counted.resource_pure _ _ _
  · have he : (Counted.lift (RandomTree.uniformBelow (sampleExponent Bmax))).Resource K
        (sampleExponent Bmax) := by
      simpa only [RandomTree.bitDepth_uniformBelow] using
        (Counted.resource_lift (RandomTree.uniformBelow (sampleExponent Bmax)) K)
    exact Counted.resource_bind _ he (fun j => Counted.resource_map _ (h _))

theorem resource_orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {K : ℕ} (hK : LowerResource lower K)
    (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).Resource K ((Nat.clog 2 I.width + 1) * sampleExponent Bmax) := by
  rw [orient]
  split_ifs with hB
  · exact Counted.resource_pure _ _ _
  · have hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
    have hs := globalS_large Bmax
    have hr := (I.radius_bounds hb).2.2.2
    have hc := clog_double_decrease (by omega : 1 < I.width) (by omega : 2 * (2 * I.E) ≤ I.width)
    have hcenter : (centerSteps P hR lower I hb (globalS Bmax) I.midpoint).Resource K 0 := by
      with_reducible exact resource_centerSteps P hR lower hK I hb (globalS Bmax) I.midpoint
    have hchild : ∀ q : BoxVector I,
        (orient G P hR lower (I.wideCentered hb q.val)).Resource K
          ((Nat.clog 2 (2 * I.E) + 1) * sampleExponent Bmax) := by
      intro q
      exact resource_orient G P hR lower hK (I.wideCentered hb q.val)
    have htail := fun qs => resource_orientationTail G P I qs _ hchild
    have hbnd : ((centerSteps P hR lower I hb (globalS Bmax) I.midpoint).bind
        (fun qs => orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hb q.val)))).Resource K (0 + (sampleExponent Bmax +
          (Nat.clog 2 (2 * I.E) + 1) * sampleExponent Bmax)) := by
      with_reducible exact Counted.resource_bind _ hcenter htail
    have hi : 0 + (sampleExponent Bmax + (Nat.clog 2 (2 * I.E) + 1) * sampleExponent Bmax) ≤
        (Nat.clog 2 I.width + 1) * sampleExponent Bmax := by
      calc
        _ = (Nat.clog 2 (2 * I.E) + 1 + 1) * sampleExponent Bmax := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1)
    dsimp only
    with_reducible exact Counted.resource_mono hbnd hi
termination_by I.width
 decreasing_by exact I.E_smaller

theorem resource_orient_global (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {K : ℕ} (hK : LowerResource lower K)
    (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).Resource K ((globalG Bmax + 1) * sampleExponent Bmax) := by
  apply Counted.resource_mono (resource_orient G P hR lower hK I)
  apply Nat.mul_le_mul_right
  have hh := Nat.clog_mono_right 2 (show I.width ≤ Bmax + 1 from I.bounded.trans (Nat.le_succ Bmax))
  unfold globalG
  omega

theorem resource_tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {K : ℕ} (hK : LowerResource lower K)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) :
    (tighten P hR lower I hB).Resource K 0 := by
  rw [tighten]
  apply Counted.resource_bind _ (F := 0) (SolveBox.resource_repeated _ (hK _ _ _) _)
  intro r₁
  split_ifs with h₁
  · exact Counted.resource_map _ (resource_tighten P hR lower hK (I.withFloor r₁) hB)
  · apply Counted.resource_bind _ (F := 0) (SolveBox.resource_repeated _ (hK _ _ _) _)
    intro r₂
    split_ifs with h₂
    · exact Counted.resource_map _ (resource_tighten P hR lower hK (I.withCeiling r₂) hB)
    · exact Counted.resource_pure _ _ _
termination_by volume I.b I.a
 decreasing_by
  · have hv := volume_floor_drop I r₁ h₁
    have hd := I.delta_positive hB
    omega
  · have hv := volume_ceiling_drop I r₂ h₂
    have hd := I.delta_positive hB
    omega

theorem resource_finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) {K : ℕ}
    (hK : LowerResource lower K) (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    (O : Orientation P)
    (up : Counted (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Counted (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    (hu : up.Resource K 0) (hl : lo.Resource K 0) :
    (finishChoice G P hR lower I hB O up lo).Resource K 0 := by
  unfold finishChoice
  split_ifs
  · exact Counted.resource_bind _
      (Counted.resource_traverse _ (fun H => I.resource_repeated (hK _ _ _) _) _)
      (fun _ => Counted.resource_map _ hu)
  · exact Counted.resource_bind _
      (Counted.resource_traverse _ (fun H => I.resource_repeated (hK _ _ _) _) _)
      (fun _ => Counted.resource_map _ hl)

theorem resource_solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P)
    (hK : LowerResource lower (nodeRandomBound G.n Bmax)) (I : SolveBox G.n Bmax) :
    (solveWidth G P hR lower I).Resource (nodeRandomBound G.n Bmax) 0 := by
  rw [solveWidth]
  apply Counted.resource_charge
  split_ifs with hB
  · exact Counted.resource_pure _ _ _
  · have hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
    have hzero := resource_tighten P hR lower hK I hb
    apply Counted.resource_mono (Counted.resource_bind _ (F := nodeRandomBound G.n Bmax) hzero ?_) (by omega)
    intro T
    have hbT : 128 * globalS Bmax < T.box.width := by rw [T.width_eq]; omega
    have ho : (orientPlus (orient G P hR lower T.box) (globalJ G.n Bmax)).Resource
        (nodeRandomBound G.n Bmax) (nodeRandomBound G.n Bmax) :=
      Counted.resource_map _ (Counted.resource_trials (resource_orient_global G P hR lower hK T.box) _)
    have hf : ∀ O : Orientation P,
        (finishChoice G P hR lower T.box hbT O
          (solveWidth G P hR lower (T.box.capHigh T.box.C T.box.C_positive (T.box.C_smaller hbT).le))
          (solveWidth G P hR lower (T.box.capLow T.box.C T.box.C_positive (T.box.C_smaller hbT).le))).Resource (nodeRandomBound G.n Bmax) 0 := by
      intro O
      exact resource_finishChoice G P hR lower hK T.box hbT O _ _
        (resource_solveWidth G P hR lower hK _)
        (resource_solveWidth G P hR lower hK _)
    simpa only [Nat.add_zero] using Counted.resource_bind _ ho
      (fun O => Counted.resource_map T.include (hf O))
termination_by I.width
 decreasing_by
  all_goals
    change T.box.C < I.width
    rw [← T.width_eq]
    exact T.box.C_smaller (by rw [T.width_eq]; omega)

theorem resource_solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    (solve G P I).Resource (nodeRandomBound G.n Bmax) 0 := by
  rw [solve]
  split_ifs with hR
  · exact Counted.resource_charge (Counted.resource_pure _ _ _)
  · apply resource_solveWidth
    intro Q h K
    exact resource_solve G Q K
termination_by parameterRank P.parameter

theorem solve_bitDepth (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    (MeanPayoff.solve G P I).bitDepth ≤ nodeRandomBound G.n Bmax *
      callBound G.n Bmax (parameterRank P.parameter) := by
  rw [← erase_solve G P I]
  simpa only [Nat.add_zero] using Counted.depth_le (resource_solve G P I) (bounded_solve G P I)

end CountedAlgorithm


theorem nodeRandomBound_scale {n B X : ℕ} (hX : 32 ≤ X) (hn : n + 1 ≤ X)
    (hg : globalG B + 1 ≤ X) (hs : globalS B ≤ X) : nodeRandomBound n B ≤ X ^ 16 := by
  have he : sampleExponent B ≤ X :=
    (Nat.le_of_lt (Nat.lt_two_pow_self)).trans hs
  have hm := Nat.mul_le_mul (globalJ_scale hX hn hs) (Nat.mul_le_mul hg he)
  have hp : X ^ 14 * (X * X) = X ^ 16 := by ring
  exact hp ▸ hm

noncomputable def rootRandomBound (G : Game) : ℕ :=
  nodeRandomBound G.n (topWidth G).toNat * rootInvocationBound G

theorem game_bitDepth (G : Game) : (gameSolve G).bitDepth ≤ rootRandomBound G := by
  simpa only [gameSolve, RandomTree.bitDepth_map, rootRandomBound, rootInvocationBound] using
    CountedAlgorithm.solve_bitDepth G (rootBudgets G) (rootBox G)

theorem rootRandomBound_nat (G : Game) :
    rootRandomBound G ≤ 2 ^ (24400 * (Nat.clog 2 ((input G).length + 2)) ^ 2) := by
  let h := Nat.clog 2 ((input G).length + 2)
  have hh : 1 ≤ h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr
    simp only [pow_zero]; omega
  have hp := Nat.le_pow_clog (by norm_num : 1 < 2) ((input G).length + 2)
  have hx : inputScale G ≤ 2 ^ (24 + h) := by
    simpa only [inputScale, pow_add] using Nat.mul_le_mul_left (2 ^ 24) hp
  have hn := nodeRandomBound_scale (inputScale_large G) (inputScale_n G)
    (inputScale_g G) (inputScale_s G)
  have hn' : nodeRandomBound G.n (topWidth G).toNat ≤ 2 ^ ((24 + h) * 16) := by
    exact hn.trans (by simpa only [← pow_mul] using Nat.pow_le_pow_left hx 16)
  have hi := Nat.mul_le_mul hn' (rootInvocationBound_nat G)
  rw [← pow_add] at hi
  apply hi.trans
  apply Nat.pow_le_pow_right (by norm_num)
  change (24 + h) * 16 + 24000 * h ^ 2 ≤ 24400 * h ^ 2
  nlinarith only [hh]

theorem rootRandomBound_real (G : Game) :
    (rootRandomBound G : ℝ) ≤
      (2 : ℝ) ^ (100000 * (Real.logb 2 ((input G).length + 2)) ^ 2) := by
  have hcast : (rootRandomBound G : ℝ) ≤
      (2 : ℝ) ^ (24400 * (Nat.clog 2 ((input G).length + 2)) ^ 2) := by
    exact_mod_cast rootRandomBound_nat G
  have hc := clog_real_le_twice_logb (input G).length
  have hc0 : (0 : ℝ) ≤ (Nat.clog 2 ((input G).length + 2) : ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.logb 2 ((input G).length + 2) := by linarith only [hc, hc0]
  have hs : 24400 * ((Nat.clog 2 ((input G).length + 2) : ℝ)) ^ 2 ≤
      100000 * (Real.logb 2 ((input G).length + 2)) ^ 2 := by nlinarith only [hc, hc0, hl0]
  apply hcast.trans
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hs

open scoped Classical

theorem game_bounded_randomness_success (G : Game) :
    (rootRandomBound G : ℝ) ≤
      (2 : ℝ) ^ (100000 * (Real.logb 2 ((input G).length + 2)) ^ 2) ∧
    7 * 2 ^ rootRandomBound G ≤ 8 * (Finset.univ.filter
      (fun bits : Fin (rootRandomBound G) → Bool =>
        CorrectSet G ((gameSolve G).readPrefix bits))).card := by
  classical
  exact ⟨rootRandomBound_real G, RandomTree.game_prefix_success G _ (game_bitDepth G)⟩

end MeanPayoff

namespace MeanPayoff
namespace BinaryInput

def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (bitsValue bs)

@[simp] theorem bitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => rw [Nat.bits_append_bit n b h, bitsValue, ih]

def readLength : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: bs => some (0, bs)
  | true :: bs => (readLength bs).map (fun p => (p.1 + 1, p.2))

@[simp] theorem readLength_replicate (k : ℕ) (bs : List Bool) :
    readLength (List.replicate k true ++ false :: bs) = some (k, bs) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, readLength, ih, Option.map_some]

def readNat (code : List Bool) : Option (ℕ × List Bool) := do
  let (k, bs) ← readLength code
  if k ≤ bs.length then
    let v := bitsValue (bs.take k)
    if 0 < v then some (v - 1, bs.drop k) else none
  else none

@[simp] theorem readNat_encode (n : ℕ) (bs : List Bool) :
    readNat (encodeNat n ++ bs) = some (n, bs) := by
  simp [readNat, encodeNat, List.append_assoc]

def readInt : List Bool → Option (ℤ × List Bool)
  | [] => none
  | sign :: bs => (readNat bs).map (fun p => (if sign then -(p.1 : ℤ) else p.1, p.2))

@[simp] theorem readInt_encode (z : ℤ) (bs : List Bool) :
    readInt (encodeInt z ++ bs) = some (z, bs) := by
  simp only [encodeInt, List.cons_append, readInt, readNat_encode, Option.map_some]
  congr 2
  by_cases hz : z < 0
  · simp [hz, abs_of_neg hz]
  · simp [hz, abs_of_nonneg (le_of_not_gt hz)]

abbrev Edge := ℕ × ℕ × ℤ

def encodeEdge (e : Edge) : List Bool := encodeNat (e.1 + 1) ++ encodeNat (e.2.1 + 1) ++ encodeInt e.2.2

def readEdge (bs : List Bool) : Option (Edge × List Bool) := do
  let (a, bs) ← readNat bs
  let (b, bs) ← readNat bs
  let (w, bs) ← readInt bs
  if 0 < a ∧ 0 < b then some ((a - 1, b - 1, w), bs) else none

@[simp] theorem readEdge_encode (e : Edge) (bs : List Bool) :
    readEdge (encodeEdge e ++ bs) = some (e, bs) := by
  rcases e with ⟨a, b, w⟩
  simp [readEdge, encodeEdge, List.append_assoc]

def readEdges : ℕ → List Bool → Option (List Edge × List Bool)
  | 0, bs => some ([], bs)
  | k + 1, bs => do
    let (e, bs) ← readEdge bs
    let (es, bs) ← readEdges k bs
    some (e :: es, bs)

@[simp] theorem readEdges_encode (es : List Edge) (bs : List Bool) :
    readEdges es.length ((es.map encodeEdge).flatten ++ bs) = some (es, bs) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [readEdges, List.append_assoc, ih]

structure RawGame where
  n : ℕ
  m : ℕ
  owner : List Bool
  edges : List Edge
  deriving DecidableEq

def lower (G : Game) : RawGame where
  n := G.n
  m := G.m
  owner := List.ofFn G.maxOwner
  edges := List.ofFn (fun e : Fin G.m => ((G.tail e).val, (G.head e).val, G.weight e))

def rawCode (R : RawGame) : List Bool :=
  encodeNat R.n ++ encodeNat R.m ++ R.owner ++ (R.edges.map encodeEdge).flatten

theorem rawCode_lower (G : Game) : rawCode (lower G) = input G := by
  simp [rawCode, lower, input, List.map_ofFn, Function.comp_def, encodeEdge]

def readRaw (bs : List Bool) : Option (RawGame × List Bool) := do
  let (n, bs) ← readNat bs
  let (m, bs) ← readNat bs
  if n ≤ bs.length then
    let owner := bs.take n
    let (es, rest) ← readEdges m (bs.drop n)
    some (⟨n, m, owner, es⟩, rest)
  else none

@[simp] theorem readRaw_code (R : RawGame) (h : R.owner.length = R.n) (he : R.edges.length = R.m) (bs : List Bool) :
    readRaw (rawCode R ++ bs) = some (R, bs) := by
  cases R with
  | mk n m owner edges =>
    dsimp only at h he
    subst n m
    simp [readRaw, rawCode, List.append_assoc]

theorem readRaw_input (G : Game) : readRaw (input G) = some (lower G, []) := by
  rw [← rawCode_lower G]
  simpa only [List.append_nil] using readRaw_code (lower G) (by simp [lower]) (by simp [lower]) []

def RawGame.Valid (R : RawGame) : Prop :=
  0 < R.n ∧ R.owner.length = R.n ∧ R.edges.length = R.m ∧
  (∀ e ∈ R.edges, e.1 < R.n ∧ e.2.1 < R.n) ∧
  ∀ v : Fin R.n, ∃ e ∈ R.edges, e.1 = v.val

instance (R : RawGame) : Decidable R.Valid := by unfold RawGame.Valid; infer_instance

theorem lower_valid (G : Game) : (lower G).Valid := by
  refine ⟨G.positive, by simp [lower], by simp [lower], ?_, ?_⟩
  · intro e he
    simp only [lower, List.mem_ofFn] at he
    obtain ⟨j, rfl⟩ := he
    exact ⟨(G.tail j).isLt, (G.head j).isLt⟩
  · intro v
    obtain ⟨e, he⟩ := G.total v
    refine ⟨((G.tail e).val, (G.head e).val, G.weight e), ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨e, rfl⟩
    · exact congrArg Fin.val he

def RawGame.toGame (R : RawGame) (h : R.Valid) : Game where
  n := R.n
  positive := h.1
  m := R.m
  tail e := ⟨(R.edges[e.val]'(by rw [h.2.2.1]; exact e.isLt)).1, (h.2.2.2.1 _ (List.getElem_mem _)).1⟩
  head e := ⟨(R.edges[e.val]'(by rw [h.2.2.1]; exact e.isLt)).2.1, (h.2.2.2.1 _ (List.getElem_mem _)).2⟩
  maxOwner v := R.owner[v.val]'(by rw [h.2.1]; exact v.isLt)
  weight e := (R.edges[e.val]'(by rw [h.2.2.1]; exact e.isLt)).2.2
  total v := by
    obtain ⟨e, he, hv⟩ := h.2.2.2.2 v
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp he
    refine ⟨⟨i, by rw [← h.2.2.1]; exact hi⟩, ?_⟩
    apply Fin.ext
    change (R.edges[i]).1 = v.val
    rw [heq, hv]

theorem toGame_lower (G : Game) (h : (lower G).Valid) : (lower G).toGame h = G := by
  cases G with
  | mk n positive m tail head owner weight total =>
    simp only [lower, RawGame.toGame, List.getElem_ofFn]

def decodeGame (bs : List Bool) : Option Game := do
  let (R, rest) ← readRaw bs
  if rest = [] then
    if h : R.Valid then some (R.toGame h) else none
  else none

@[simp] theorem decodeGame_input (G : Game) : decodeGame (input G) = some G := by
  simp [decodeGame, readRaw_input, lower_valid, toGame_lower]

def programTree (bs : List Bool) : RandomTree (List Bool) :=
  match decodeGame bs with
  | none => .leaf []
  | some G => (gameSolve G).map List.ofFn

@[simp] theorem programTree_input (G : Game) :
    programTree (input G) = (gameSolve G).map List.ofFn := by
  simp [programTree]

end BinaryInput
end MeanPayoff
end

end OAI
