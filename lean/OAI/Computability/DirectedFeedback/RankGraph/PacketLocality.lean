import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.AllGraph

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketLocality
open Construction SourceProbability FiniteDistribution Games RankGraph PacketSeeds
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

abbrev Slots (T : Nat) := Fin (T+1)
def localGame (f : Slots T → X ≃ Y × Bool) : Game (Slots T) (Slots T) (Slots T) X Y where
  edgeLaw := uniform _
  left := id
  right := id
  project e x := (f e x).1

variable (G : Game U V E X Y) (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (s : Seed X Y M T N) (e : Slots T → E) (a : U → X) (b : V → Y)

lemma comp_snoc {t : Nat} {A B : Type} (f : A → B) (v : Fin t → A) (w : A) :
    (fun i : Fin (t+1) => f ((Fin.snoc v w : Fin (t+1) → A) i))=Fin.snoc (fun i => f (v i)) (f w) := Fin.comp_snoc _ _ _

lemma map_snoc_apply {t : Nat} {A B : Type} (f : A → B) (v : Fin t → A) (w : A) (i : Fin (t+1)) :
    f ((Fin.snoc v w : Fin (t+1) → A) i)= (Fin.snoc (fun i => f (v i)) (f w) : Fin (t+1) → B) i :=
  congrFun (Fin.comp_snoc f v w) i

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
lemma deleted_fill :
    AllLabels.deleted G hYX fiber a b (fill G s e) ↔
    AllLabels.deleted (localGame (fiber ∘ e)) hYX (fiber ∘ e)
      (a ∘ G.left ∘ e) (b ∘ G.right ∘ e) (fill (localGame (fiber ∘ e)) s id) := by
  rcases s with s | (s | (s | s))
  · rfl
  · simp +unfoldPartialApp only [AllLabels.deleted,TestGraph.LabelDeleted,fill,fillBig,fillCommon,fillPrefix,fresh,
      wildcard,bigWildcard,labels,vertices,localGame,map_snoc_apply,Function.comp_def,id_eq]
    rfl
  · rfl
  · simp +unfoldPartialApp only [AllLabels.deleted,TestGraph.LabelDeleted,fill,fillCompare,comparison,
      fillCommon,fillPrefix,fresh,localGame,twoLevel,eval_vertex,labels,vertices,
      map_snoc_apply,Function.comp_def,id_eq]
    rfl

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
lemma height_fill :
    AllLabels.height G hYX fiber a b (fill G s e) =
    AllLabels.height (localGame (fiber ∘ e)) hYX (fiber ∘ e)
      (a ∘ G.left ∘ e) (b ∘ G.right ∘ e) (fill (localGame (fiber ∘ e)) s id) := by
  rcases s with s | (s | (s | s))
  · rfl
  · simp +unfoldPartialApp only [AllLabels.height,fill,fillBig,fillCommon,fillPrefix,fresh,
      wildcard,bigWildcard,labels,vertices,localGame,map_snoc_apply,Function.comp_def,id_eq]
    rfl
  · rfl
  · simp +unfoldPartialApp only [AllLabels.height,fill,fillCompare,comparison,
      fillCommon,fillPrefix,fresh,localGame,twoLevel,eval_vertex,labels,vertices,
      map_snoc_apply,Function.comp_def,id_eq]
    rfl

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
lemma code_fill :
    AllLabels.code G hYX fiber a b (fill G s e) =
    AllLabels.code (localGame (fiber ∘ e)) hYX (fiber ∘ e)
      (a ∘ G.left ∘ e) (b ∘ G.right ∘ e) (fill (localGame (fiber ∘ e)) s id) := by
  unfold AllLabels.code
  rw [deleted_fill G hYX fiber s e a b]
  split_ifs
  · rfl
  · congr 2
    exact height_fill G hYX fiber s e a b

end DirectedFeedback.PacketLocality

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open BoundedExpr Construction PacketSeeds Games RankGraph
variable (q M T N : Nat) [NeZero q] [NeZero M] [NeZero T] [NeZero N]
abbrev X := Fin q × Bool
abbrev Y := Fin q
abbrev Shape := RankPackets.Shape (X q) (Y q) T N
abbrev Seed := PacketSeeds.Seed (X q) (Y q) M T N
abbrev Tag := Shape q T N ⊕ Seed q M T N
instance tagNonempty : Nonempty (Tag q M T N) := ⟨.inl (.inl ⟨0,fun _ => 0⟩)⟩
omit [NeZero q] in
theorem hYX : Fintype.card (Y q) ≤ Fintype.card (X q) := by simp [X,Y,Fintype.card_prod]; omega
variable (D C : Nat) (c : Seed q M T N → Nat)
def scale (x : List Bool) : Nat := C*(GameRead.m x)^(T+1)
def r (x : List Bool) : Nat := scale T C x*(D+1)
def base (x : List Bool) := SumBox.base (GameRead.n x) (GameRead.m x)
def copies (x : List Bool) := SumBox.copies (r T D C x) c

def size (x : List Bool) := SumBox.size (Shape q T N) (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c
def tag (x : List Bool) (i : Nat) := SumBox.tag (Shape q T N) (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c i
def digit (x : List Bool) (i : Nat) (j : Fin (T+1)) := SumBox.digits (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c i j
def copy (x : List Bool) (i : Nat) := SumBox.copy (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c i
def valid (x : List Bool) (i : Nat) := SumBox.valid (Shape q T N) (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c i

def isRank : Tag q M T N → Prop | .inl _ => True | .inr _ => False
def u (x : List Bool) (i : Nat) (j : Fin (T+1)) : Nat :=
  if isRank q M T N (tag q M T N D C c x i) then digit q M T N D C c x i j
  else GameRead.left q x (digit q M T N D C c x i j)
def v (x : List Bool) (i : Nat) (j : Fin (T+1)) : Nat :=
  if isRank q M T N (tag q M T N D C c x i) then digit q M T N D C c x i j
  else GameRead.right q x (digit q M T N D C c x i j)

def tagRule (s : Tag q M T N) (f : Fin (T+1) → X q ≃ Y q × Bool) :
    LocalPrinter.Rule (Fin (T+1)) (Fin (T+1)) (X q) (Y q) (2*N+1) := fun a b =>
  AllLabels.code (PacketLocality.localGame f) (hYX q) f a b
    (match s with
    | .inl r => .inl (RankPackets.fill r id)
    | .inr s => PacketSeeds.fill (PacketLocality.localGame f) s id)
def rule (x : List Bool) (i : Nat) := tagRule q M T N (tag q M T N D C c x i)
  (fun j => GameRead.fiber q x (digit q M T N D C c x i j))

omit [NeZero T] in
theorem scale_def (s : Nat) : Def (r:=s) (fun x _ => scale T C x) :=
  (Def.lit C).mul ((GameRead.m_def s).pow (T+1))
omit [NeZero T] in
theorem r_def (s : Nat) : Def (r:=s) (fun x _ => r T D C x) :=
  (scale_def T C s).mul (Def.lit (D+1))
theorem base_def (s : Nat) : Def (r:=s) (fun x _ => base x) :=
  ((GameRead.n_def s).add (GameRead.m_def s)).add (Def.lit 1)
omit [NeZero q] [NeZero M] [NeZero T] [NeZero N] in
theorem copies_def (s : Nat) : Def (r:=s) (fun x _ => copies q M T N D C c x) :=
  ((r_def T D C s).add (Def.lit (∑ s,c s))).add (Def.lit 1)
omit [NeZero q] [NeZero M] [NeZero T] [NeZero N] in
theorem size_def : Def (r:=0) (fun x _ => size q M T N D C c x) :=
  (Def.lit (Fintype.card (Tag q M T N))).mul
    (((base_def 0).pow (T+1)).mul (copies_def q M T N D C c 0))
omit [NeZero q] [NeZero M] [NeZero T] in
theorem tag_def : FDef (r:=1) (fun x a => tag q M T N D C c x (a 0)) :=
  BoxCodec.tag_def _ (base_def 1) (copies_def q M T N D C c 1) (Def.arg 0) (T+1)
omit [NeZero q] [NeZero M] [NeZero T] [NeZero N] in
theorem digit_def (j : Fin (T+1)) : Def (r:=1) (fun x a => digit q M T N D C c x (a 0) j) :=
  BoxCodec.digits_def (base_def 1) (copies_def q M T N D C c 1) (Def.arg 0) (T+1) j
omit [NeZero q] [NeZero M] [NeZero T] [NeZero N] in
theorem copy_def : Def (r:=1) (fun x a => copy q M T N D C c x (a 0)) :=
  BoxCodec.copy_def (base_def 1) (copies_def q M T N D C c 1) (Def.arg 0) (T+1)
omit [NeZero q] [NeZero M] [NeZero T] in
theorem isRank_def : PDef (r:=1) (fun x a => isRank q M T N (tag q M T N D C c x (a 0))) :=
  (tag_def q M T N D C c).toDef (fun s => if isRank q M T N s then 1 else 0)
omit [NeZero q] [NeZero M] [NeZero T] in
theorem u_def (j : Fin (T+1)) : Def (r:=1) (fun x a => u q M T N D C c x (a 0) j) :=
  (isRank_def q M T N D C c).nite (digit_def q M T N D C c j)
    (GameRead.left_def q (digit_def q M T N D C c j))
omit [NeZero q] [NeZero M] [NeZero T] in
theorem v_def (j : Fin (T+1)) : Def (r:=1) (fun x a => v q M T N D C c x (a 0) j) :=
  (isRank_def q M T N D C c).nite (digit_def q M T N D C c j)
    (GameRead.right_def q (digit_def q M T N D C c j))
omit [NeZero M] [NeZero T] in
theorem rule_def : FDef (r:=1) (fun x a => rule q M T N D C c x (a 0)) :=
  ((tag_def q M T N D C c).pair (FDef.pi (fun j =>
    GameRead.fiber_def q (digit_def q M T N D C c j)))).map (fun z => tagRule q M T N z.1 z.2)
omit [NeZero q] [NeZero M] [NeZero T] in
theorem valid_def : PDef (r:=1) (fun x a => valid q M T N D C c x (a 0)) := by
  let f : Tag q M T N → Nat := Sum.elim (fun _ => 0) c
  have ht := tag_def q M T N D C c
  have hd := digit_def q M T N D C c
  have hj := copy_def q M T N D C c
  have hi := isRank_def q M T N D C c
  have h := (hi.and ((PDef.all (fun j => PDef.lt (hd j) (GameRead.n_def 1))).and
      (PDef.lt hj (r_def T D C 1)))).or
    (hi.not.and ((PDef.all (fun j => PDef.lt (hd j) (GameRead.m_def 1))).and
      (PDef.lt hj (ht.toDef f))))
  apply h.congr
  intro x a
  unfold valid SumBox.valid
  simp only [tag,digit,copy]
  cases SumBox.tag (Shape q T N) (Seed q M T N) (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c (a 0) <;> simp [isRank,f]

def family (hC : 0<C) : LocalPrinter.Family (Fin (T+1)) (Fin (T+1)) (X q) (Y q) (2*N+1) where
  n := size q M T N D C c
  k := fun x => 4*scale T C x
  valid := valid q M T N D C c
  u := u q M T N D C c
  v := v q M T N D C c
  rule := rule q M T N D C c
  n_def := size_def q M T N D C c
  k_def := (Def.lit 4).mul (scale_def T C 0)
  valid_def := valid_def q M T N D C c
  u_def := u_def q M T N D C c
  v_def := v_def q M T N D C c
  rule_def := rule_def q M T N D C c
  k_pos x := by unfold scale; have := GameRead.m_pos x; positivity

end DirectedFeedback.RawFamily

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketSeeds
open SourceProbability FiniteDistribution Construction PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]
variable (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

def mass (H K : Nat) : Seed X Y M T N → ℝ
  | .inl s => H*(fullLaw ψLaw).weight s
  | .inr (.inl s) => Fintype.card X*(bigLaw ψLaw).weight s
  | .inr (.inr (.inl s)) => Fintype.card Y*(smallLaw ψLaw).weight s
  | .inr (.inr (.inr s)) => K*(compareLaw ψLaw).weight s

theorem mass_nonnegative (H K : Nat) (s : Seed X Y M T N) : 0 ≤ mass ψLaw H K s := by
  rcases s with s | (s | (s | s)) <;> exact mul_nonneg (Nat.cast_nonneg _) (FiniteDistribution.nonnegative _ _)

omit [Nonempty X] in
theorem slot_rational : (slotLaw (X:=X) (M:=M)).RationalMass :=
  RationalMass.uniform.sigma (fun i => Construction.subsetLaw_rational i)

omit [Nonempty X] in
theorem common_rational (hψ : ψLaw.RationalMass) : (commonLaw (M:=M) ψLaw).RationalMass :=
  hψ.product (RationalMass.uniform.sigma (fun _ => slot_rational.iid _))

omit [Nonempty Y] in
theorem localCompare_rational (t : Nat) : (localCompareLaw (Y:=Y) (M:=M) t).RationalMass := by
  apply RationalMass.uniform.sigma
  intro i
  apply RationalMass.uniform.product
  apply RationalMass.table
  intro _ b
  obtain ⟨⟨b₁,b₂⟩,b₃⟩ := b
  have hp : Rational (bias i) := (Rational.nat 2).inv.pow _
  have h1 := Rational.one.sub hp
  cases b₁ <;> cases b₂ <;> cases b₃ <;>
    first | exact Rational.one.sub ((Rational.nat 2).mul hp)
          | exact hp.pow 2 | exact hp.mul h1 | exact Rational.zero

theorem mass_rational (hψ : ψLaw.RationalMass) (H K : Nat) (s : Seed X Y M T N) :
    Rational (mass ψLaw H K s) := by
  rcases s with s | (s | (s | s))
  · exact (Rational.nat H).mul ((hψ.product (slot_rational.iid T)) s)
  · exact (Rational.nat _).mul (((common_rational ψLaw hψ).product
        (RationalMass.uniform.sigma (fun _ => RationalMass.uniform))) s)
  · exact (Rational.nat _).mul (((common_rational ψLaw hψ).product
        (RationalMass.uniform.sigma (fun _ => RationalMass.uniform))) s)
  · exact (Rational.nat K).mul (((common_rational ψLaw hψ).sigma
        (fun d => localCompare_rational d.2.1.val)) s)

theorem denominator (hψ : ψLaw.RationalMass) (H K : Nat) :
    ∃ C : Nat, 0<C ∧ ∃ c : Seed X Y M T N → Nat, ∀ s, (C:ℝ)*mass ψLaw H K s=c s :=
  fixed_denominator _ (mass_rational ψLaw hψ H K) (mass_nonnegative ψLaw H K)

variable (G : Game U V E X Y)

theorem moment (D H K : Nat) (f : AllVertex U V E X Y M T N → ℝ)
    (hf : ∀ r, f (.inl r)=0) :
    (∑ s, mass ψLaw H K s*(G.edgeLaw.iid (T+1)).expectation (fun e => f (fill G s e))) =
      ∑ v, allCost G ψLaw D H K v*f v := by
  have hex := sample_full ψLaw G (fun v => f (.inr (.inl (.inl v))))
  have heb := sample_big ψLaw G (fun v => f (.inr (.inl (.inr (.inl v)))))
  have hes := sample_small ψLaw G (fun v => f (.inr (.inl (.inr (.inr v)))))
  have hec := sample_compare ψLaw G (fun v => f (.inr (.inr v)))
  calc
    _ = H*(fullLaw ψLaw).expectation (fun s => (G.edgeLaw.iid (T+1)).expectation
          (fun e => f (.inr (.inl (.inl (fillFull G s e)))))) +
        (Fintype.card X)*(bigLaw ψLaw).expectation (fun s => (G.edgeLaw.iid (T+1)).expectation
          (fun e => f (.inr (.inl (.inr (.inl (fillBig G s e))))))) +
        (Fintype.card Y)*(smallLaw ψLaw).expectation (fun s => (G.edgeLaw.iid (T+1)).expectation
          (fun e => f (.inr (.inl (.inr (.inr (fillSmall G s e))))))) +
        K*(compareLaw ψLaw).expectation (fun s => (G.edgeLaw.iid (T+1)).expectation
          (fun e => f (.inr (.inr (fillCompare G s e))))) := by
      simp only [Fintype.sum_sum_type,mass,fill,expectation,Finset.mul_sum]
      ring_nf
    _ = _ := by
      rw [hex,heb,hes,hec]
      simp only [Fintype.sum_sum_type,allCost,hf,mul_zero,Finset.sum_const_zero,zero_add,
        expectation,Finset.mul_sum]
      ring_nf

theorem iid_uniform_expectation {A : Type} [Fintype A] [Nonempty A] (L : Nat) (f : (Fin L → A) → ℝ) :
    ((uniform A).iid L).expectation f = (∑ a, f a)/(Fintype.card A:ℝ)^L := by
  simp only [expectation,iid,uniform,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem integer_moment [Nonempty E] (hE : G.edgeLaw=uniform E) (D H K C : Nat)
    (c : Seed X Y M T N → Nat) (hc : ∀ s, (C:ℝ)*mass ψLaw H K s=c s)
    (f : AllVertex U V E X Y M T N → ℝ) (hf : ∀ r, f (.inl r)=0) :
    (∑ s, (c s:ℝ)*∑ e : Fin (T+1) → E, f (fill G s e)) =
      (C*(Fintype.card E)^(T+1):Nat)*(∑ v, allCost G ψLaw D H K v*f v) := by
  rw [← moment ψLaw G D H K f hf]
  simp only [hE,iid_uniform_expectation,Nat.cast_mul,Nat.cast_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hm : ((Fintype.card E:ℝ)^(T+1)) ≠ 0 := by positivity
  rw [← hc s]
  field_simp
  simp only [Finset.mul_sum]

end DirectedFeedback.PacketSeeds

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.LivePackets
open Construction SourceProbability FiniteDistribution Games RankGraph PacketSeeds
variable {W E X Y : Type} [Fintype W] [Fintype E] [Fintype X] [Fintype Y]
  [Nonempty W] [Nonempty E] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

abbrev Live (r : Nat) (c : Seed X Y M T N → Nat) :=
  ((RankPackets.Shape X Y T N × (Fin (T+1) → W)) × Fin r) ⊕
    (Σ s : Seed X Y M T N, (Fin (T+1) → E) × Fin (c s))
instance liveFintype (r : Nat) (c : Seed X Y M T N → Nat) : Fintype (Live (W:=W) (E:=E) r c) := by
  unfold Live
  infer_instance

variable (G : Game W W E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (r : Nat) (c : Seed X Y M T N → Nat)
def project : Live (W:=W) (E:=E) r c → AllVertex W W E X Y M T N
  | .inl a => .inl (RankPackets.fill a.1.1 a.1.2)
  | .inr a => PacketSeeds.fill G a.1 a.2.1

omit [Nonempty W] [Nonempty E] [Nonempty X] [Nonempty Y] [NeZero M] [NeZero T] in
theorem sum_project (f : AllVertex W W E X Y M T N → ℝ) (hf : ∀ z, f (.inl z)=0) :
    (∑ a : Live (W:=W) (E:=E) r c, f (project G r c a)) =
      ∑ s, (c s:ℝ)*∑ e : Fin (T+1) → E, f (PacketSeeds.fill G s e) := by
  simp only [Fintype.sum_sum_type,project,hf,Finset.sum_const_zero,zero_add,Fintype.sum_sigma,
    Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [Finset.mul_sum]

omit [Nonempty W] in
theorem sum_cost (hE : G.edgeLaw=uniform E) (D H K C : Nat)
    (hc : ∀ s, (C:ℝ)*mass ψLaw H K s=c s)
    (f : AllVertex W W E X Y M T N → ℝ) (hf : ∀ z, f (.inl z)=0) :
    (∑ a : Live (W:=W) (E:=E) r c, f (project G r c a)) =
      (C*(Fintype.card E)^(T+1):Nat)*(∑ v, allCost G ψLaw D H K v*f v) := by
  rw [sum_project G r c f hf]
  exact integer_moment ψLaw G hE D H K C c hc f hf

omit [Nonempty E] [Nonempty X] [Nonempty Y] [NeZero M] [NeZero T] in
theorem rank_fiber_bound (z : Rank W W X Y T N) :
    r ≤ PotentialCover.fiberCount (project G r c) (.inl z) := by
  obtain ⟨⟨s,a⟩,ha⟩ := RankPackets.fill_surjective (W:=W) (X:=X) (Y:=Y) (T:=T) (N:=N) z
  change RankPackets.fill s a=z at ha
  let f : Fin r → {v : Live (W:=W) (E:=E) r c // project G r c v=.inl z} :=
    fun j => ⟨.inl ((s,a),j),by change Sum.inl (RankPackets.fill s a)=Sum.inl z; rw [ha]⟩
  have hf : Function.Injective f := by
    intro i j h
    have := congrArg Subtype.val h
    simpa [f] using this
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hcard
  convert hcard using 1
  rw [Fintype.card_subtype]
  unfold PotentialCover.fiberCount
  congr 1
  ext v
  simp

omit [Nonempty W] in
theorem test_fiber_count (hE : G.edgeLaw=uniform E) (D H K C : Nat)
    (hc : ∀ s, (C:ℝ)*mass ψLaw H K s=c s)
    (z : Wild W W X Y M T N ⊕ Compare W E X Y M T N) :
    (PotentialCover.fiberCount (project G r c) (.inr z):ℝ) =
      (C*(Fintype.card E)^(T+1):Nat)*allCost G ψLaw D H K (.inr z) := by
  have h := sum_cost G ψLaw r c hE D H K C hc (fun v => if v=.inr z then 1 else 0)
    (fun _ => by simp)
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  rw [← h]
  simp only [PotentialCover.fiberCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem fiber_weight (hE : G.edgeLaw=uniform E) (D H K C : Nat)
    (hc : ∀ s, (C:ℝ)*mass ψLaw H K s=c s)
    (hr : C*(Fintype.card E)^(T+1)*(D+1) ≤ r)
    (v : AllVertex W W E X Y M T N) :
    (C*(Fintype.card E)^(T+1):Nat)*allCost G ψLaw D H K v ≤
      PotentialCover.fiberCount (project G r c) v := by
  cases v with
  | inl z =>
    have hh := le_trans hr (rank_fiber_bound G r c z)
    simpa only [allCost,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using
      (show (C*(Fintype.card E)^(T+1)*(D+1):Nat)≤PotentialCover.fiberCount (project G r c) (.inl z) from hh)
        |> (fun h => (Nat.cast_le (α:=ℝ)).mpr h)
  | inr z => exact (test_fiber_count G ψLaw r c hE D H K C hc z).symm.le

end DirectedFeedback.LivePackets

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.FiniteLift
variable {L B : Type} [Fintype L] [Fintype B]
variable {n : Nat} (e : L → Fin n) (he : Function.Injective e)
include he
def pull (F : Finset (Fin n)) : Finset L := Finset.univ.filter (fun a => e a ∈ F)

 theorem pull_card (F : Finset (Fin n)) : (pull e F).card ≤ F.card := by
  calc
    _ = ((pull e F).image e).card := (Finset.card_image_of_injective _ he).symm
    _ ≤ F.card := Finset.card_le_card (by intro x hx; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx; exact (Finset.mem_filter.mp ha).2)

theorem pull_feedback (R : Fin n → Fin n → Prop) (F : Finset (Fin n)) (hF : FeedbackR R F) :
    FeedbackR (fun a b => R (e a) (e b)) (pull e F) := by
  intro k f hi ha
  obtain ⟨i,hi⟩ := hF k (e ∘ f) (he.comp hi) ha
  exact ⟨i,by simp [pull] at hi ⊢; exact hi⟩

theorem feedback_cost (p : L → B) (R : B → B → Prop) (S : Fin n → Fin n → Prop)
    (hcover : ∀ a b, R (p a) (p b) → S (e a) (e b)) (w : B → ℝ) (C D : Nat)
    (hw : ∀ b, (C:ℝ)*w b ≤ PotentialCover.fiberCount p b)
    (hgap : ∀ F : Finset B, FeedbackR R F → (D:ℝ)<∑ b ∈ F,w b)
    (hC : 0<C) (F : Finset (Fin n)) (hF : FeedbackR S F) :
    (C*D:Nat) < (F.card:ℝ) := by
  have hp := pull_feedback e he S F hF
  have hb := PotentialCover.feedback_project p R (fun a b => S (e a) (e b)) hcover (pull e F) hp
  have hc := PotentialCover.weight_le_card p w C hw (pull e F)
  have hd := mul_lt_mul_of_pos_left (hgap _ hb) (show (0:ℝ)<C by exact_mod_cast hC)
  have hcard : ((pull e F).card:ℝ)≤F.card := by exact_mod_cast pull_card e he F
  rw [Nat.cast_mul]
  linarith
end DirectedFeedback.FiniteLift

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
variable {q M T N : Nat} [NeZero q] [NeZero M] [NeZero T] [NeZero N]
variable (D C : Nat) (c : Seed q M T N → Nat) (hC : 0<C) (x : List Bool)
abbrev W := Fin (GameRead.n x)
abbrev E := Fin (GameRead.m x)
instance wNonempty : Nonempty (W x) := ⟨⟨0,GameRead.n_pos x⟩⟩
instance eNonempty : Nonempty (E x) := ⟨⟨0,GameRead.m_pos x⟩⟩
abbrev Live := LivePackets.Live (W:=W x) (E:=E x) (r T D C x) c

def embed (z : Live D C c x) : Fin ((family q M T N D C c hC).n x) :=
  SumBox.embed (Shape q T N) (Seed q M T N) (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c z

omit [NeZero M] [NeZero T] in
theorem embed_injective : Function.Injective (embed D C c hC x) := SumBox.embed_injective _ _ _ _ _ _ _
omit [NeZero M] [NeZero T] in
theorem valid_embed (z : Live D C c x) : (family q M T N D C c hC).valid x (embed D C c hC x z).val :=
  SumBox.valid_embed _ _ _ _ _ _ _ z
omit [NeZero M] [NeZero T] in
theorem valid_surjective (i : Fin ((family q M T N D C c hC).n x))
    (hi : (family q M T N D C c hC).valid x i.val) : ∃z, embed D C c hC x z=i :=
  SumBox.valid_surjective _ _ _ _ _ _ _ i hi

omit [NeZero M] [NeZero T] in
theorem tag_embed (z : Live D C c x) :
    tag q M T N D C c x (embed D C c hC x z).val=
    (match z with | .inl a => .inl a.1.1 | .inr a => .inr a.1) := by
  have h := SumBox.tag_embed (Shape q T N) (Seed q M T N) (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c z
  rcases z with a | a <;> exact h

omit [NeZero M] [NeZero T] in
theorem digit_embed (z : Live D C c x) (j : Fin (T+1)) :
    digit q M T N D C c x (embed D C c hC x z).val j=
    (match z with | .inl a => (a.1.2 j).val | .inr a => (a.2.1 j).val) := by
  have h := SumBox.digits_embed (Shape q T N) (Seed q M T N) (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c z j
  rcases z with a | a <;> exact h

variable (G : Game (W x) (W x) (E x) (X q) (Y q))
variable (fiber : E x → X q ≃ Y q × Bool)
variable (hl : ∀e : E x, GameRead.left q x e.val=(G.left e).val)
variable (hr : ∀e : E x, GameRead.right q x e.val=(G.right e).val)
variable (hf : ∀e : E x, GameRead.fiber q x e.val=fiber e)
include hl hr hf

omit [NeZero M] [NeZero T] in
theorem value_embed (z : Live D C c x) (a : Nat → X q) (b : Nat → Y q) :
    (family q M T N D C c hC).value x (embed D C c hC x z).val a b=
    AllLabels.code G (hYX q) fiber (a ∘ Fin.val) (b ∘ Fin.val)
      (LivePackets.project G (r T D C x) c z) := by
  change rule q M T N D C c x (embed D C c hC x z).val
    (a ∘ u q M T N D C c x (embed D C c hC x z).val)
    (b ∘ v q M T N D C c x (embed D C c hC x z).val)=_
  unfold rule u v
  simp_rw [tag_embed D C c hC x z,digit_embed D C c hC x z]
  rcases z with ⟨⟨s,e⟩,j⟩ | ⟨s,e,j⟩
  · dsimp +instances only [isRank,tagRule,LivePackets.project]
    unfold AllLabels.code
    simp +instances only [AllLabels.deleted,TestGraph.LabelDeleted]
    congr 2
    apply Fin.ext
    change 2*(eval _ _ (RankPackets.fill s id)).val=2*(eval _ _ (RankPackets.fill s e)).val
    rw [RankPackets.eval_fill s e (a ∘ Fin.val) (b ∘ Fin.val)]
    simp +instances only [ite_true]
    rfl
  · simp only [isRank,tagRule,LivePackets.project]
    simp_rw [hl,hr,hf]
    exact (PacketLocality.code_fill G (hYX q) fiber s e (a ∘ Fin.val) (b ∘ Fin.val)).symm

omit [NeZero M] [NeZero T] in
theorem cover_arc (a b : Live D C c x)
    (h : AllArc G (hYX q) fiber (LivePackets.project G (r T D C x) c a)
      (LivePackets.project G (r T D C x) c b)) :
    (family q M T N D C c hC).Arc x (embed D C c hC x a).val (embed D C c hC x b).val := by
  rw [LocalPrinter.Family.arc_global]
  refine ⟨?_,valid_embed D C c hC x a,valid_embed D C c hC x b,?_⟩
  · intro he
    have hab := embed_injective D C c hC x (Fin.ext he)
    subst b
    exact TestGraph.arc_irrefl _ _ _ h
  · intro l k
    rw [value_embed D C c hC x G fiber hl hr hf,value_embed D C c hC x G fiber hl hr hf]
    exact AllLabels.ordered_arc G (hYX q) fiber _ _ h

def liveDeleted (a : W x → X q) (b : W x → Y q) : Finset (Live D C c x) :=
  Finset.univ.filter (fun z => AllLabels.deleted G (hYX q) fiber a b (LivePackets.project G (r T D C x) c z))

omit [NeZero M] [NeZero T] in
theorem deleted_eq_image (a : Nat → X q) (b : Nat → Y q) :
    (family q M T N D C c hC).deleted x a b =
    (liveDeleted D C c x G fiber (a ∘ Fin.val) (b ∘ Fin.val)).image (embed D C c hC x) := by
  ext i
  constructor
  · intro hi
    obtain ⟨hv,hd⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨z,rfl⟩ := valid_surjective D C c hC x i hv
    refine Finset.mem_image.mpr ⟨z,?_,rfl⟩
    rw [value_embed D C c hC x G fiber hl hr hf] at hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(AllLabels.code_none _ _ _ _ _ _).mp hd⟩
  · intro hi
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,valid_embed D C c hC x z,?_⟩
    rw [value_embed D C c hC x G fiber hl hr hf]
    exact (AllLabels.code_none _ _ _ _ _ _).mpr (Finset.mem_filter.mp hz).2

end DirectedFeedback.RawFamily

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
variable {q D : Nat} [NeZero q] (P : Parameters D) (R : RankParameters P (X q)) [NeZero R.N]
variable (C : Nat) (c : Seed q P.M P.T R.N → Nat) (hC : 0<C)
variable (hc : ∀s, (C:ℝ)*mass R.law (8*(D+1)) P.K s=c s)
variable (x : List Bool)
variable (G : Game (W x) (W x) (E x) (X q) (Y q))
variable (fiber : E x → X q ≃ Y q × Bool)
variable (hl : ∀e : E x, GameRead.left q x e.val=(G.left e).val)
variable (hr : ∀e : E x, GameRead.right q x e.val=(G.right e).val)
variable (hf : ∀e : E x, GameRead.fiber q x e.val=fiber e)
variable (hE : G.edgeLaw=uniform (E x))
variable (hproj : ∀e a, (fiber e a).1=G.project e a)

def extend {n : Nat} {A : Type} [Nonempty A] (a : Fin n → A) (i : Nat) : A :=
  if h : i<n then a ⟨i,h⟩ else Classical.choice inferInstance
@[simp] theorem extend_restrict {n : Nat} {A : Type} [Nonempty A] (a : Fin n → A) :
    extend a ∘ Fin.val=a := by funext i; simp [extend]

theorem feedback_printer_iff (F : Finset (Fin ((family q P.M P.T R.N D C c hC).n x))) :
    ((family q P.M P.T R.N D C c hC).printer.graph x).Feedback F ↔
    FeedbackR (fun i j => (family q P.M P.T R.N D C c hC).Arc x i.val j.val) F := by
  let Pn := (family q P.M P.T R.N D C c hC).printer
  constructor
  · intro h n f hi ha
    apply h n f
    exact ⟨hi,fun i => (Pn.mem_pairs x _ _).mpr (ha i)⟩
  · intro h n f hh
    exact h n f hh.1 (fun i => (Pn.mem_pairs x _ _).mp (hh.2 i))

include hc hE hproj in
omit [NeZero R.N] in
theorem live_card_bound (a : W x → X q) (b : W x → Y q)
    (hscore : 1-(P.theta:ℝ)≤G.score a b) :
    ((liveDeleted D C c x G fiber a b).card:ℝ) ≤ 4*scale P.T C x := by
  have hsum := LivePackets.sum_cost G R.law (r P.T D C x) c hE D (8*(D+1)) P.K C hc
    (fun v => if AllLabels.deleted G (hYX q) fiber a b v then 1 else 0)
    (fun z => by simp [AllLabels.deleted,TestGraph.LabelDeleted])
  have hbound := AllLabels.completeness P R G (hYX q) fiber hproj a b hscore
  have hcard : ((liveDeleted D C c x G fiber a b).card:ℝ)=
      ∑ z : Live D C c x, (if AllLabels.deleted G (hYX q) fiber a b (LivePackets.project G (r P.T D C x) c z) then 1 else 0) := by
    simp only [liveDeleted,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hcard,hsum]
  simp only [Fintype.card_fin,E,mul_ite,mul_one,mul_zero,Nat.cast_mul,Nat.cast_add,Nat.cast_one,scale,Nat.cast_ofNat,Nat.cast_pow]
  have hs : (0:ℝ)≤C*(GameRead.m x)^(P.T+1) := by positivity
  have hh := mul_le_mul_of_nonneg_left hbound hs
  convert hh using 1; first | rfl | ring

include hc hl hr hf hE hproj in
theorem completeness (a : W x → X q) (b : W x → Y q)
    (hscore : 1-(P.theta:ℝ)≤G.score a b) :
    ((family q P.M P.T R.N D C c hC).printer.graph x).dfvs ≤ 4*scale P.T C x := by
  let F := family q P.M P.T R.N D C c hC
  have hfb := F.deleted_feedback x (extend a) (extend b)
  have he := deleted_eq_image D C c hC x G fiber hl hr hf (extend a) (extend b)
  simp only [extend_restrict] at he
  have hcard := Finset.card_image_le (s:=liveDeleted D C c x G fiber a b) (f:=embed D C c hC x)
  have hb := live_card_bound P R C c hc x G fiber hE hproj a b hscore
  apply (Digraph.dfvs_le_iff _ _).mpr
  refine ⟨F.deleted x (extend a) (extend b),?_,?_⟩
  · exact (feedback_printer_iff P R C c hC x _).mpr hfb
  · change (F.deleted x (extend a) (extend b)).card≤_
    rw [he]
    have hnat : (liveDeleted D C c x G fiber a b).card≤4*scale P.T C x := by exact_mod_cast hb
    exact hcard.trans hnat

include hc hl hr hf hE hproj in
theorem soundness (hsound : G.Sound P.theta) :
    (D*scale P.T C x:Nat) < (((family q P.M P.T R.N D C c hC).printer.graph x).dfvs:ℝ) := by
  let F := family q P.M P.T R.N D C c hC
  obtain ⟨Q,hQ,hcard⟩ := Digraph.dfvs_attained (F.printer.graph x)
  have hfib := LivePackets.fiber_weight G R.law (r P.T D C x) c hE D (8*(D+1)) P.K C hc
    (by simp only [r,scale,E,Fintype.card_fin]; exact le_rfl)
  have hgap := all_soundness G P R (hYX q) fiber hproj hsound
  have hcast : ((8*(D+1):Nat):ℝ)=8*((D:ℝ)+1) := by push_cast; rfl
  rw [hcast] at hfib
  have hs : 0<scale P.T C x := by unfold scale; have hm := GameRead.m_pos x; positivity
  have hh := FiniteLift.feedback_cost (embed D C c hC x) (embed_injective D C c hC x)
    (LivePackets.project G (r P.T D C x) c) (AllArc G (hYX q) fiber)
    (fun i j => F.Arc x i.val j.val)
    (cover_arc D C c hC x G fiber hl hr hf)
    (allCost G R.law D (8*((D:ℝ)+1)) P.K) (scale P.T C x) D
    (by simpa only [scale,E,Fintype.card_fin] using hfib)
    hgap hs Q ((feedback_printer_iff P R C c hC x Q).mp hQ)
  have hh' := lt_of_lt_of_eq hh (congrArg (fun n : Nat => (n:ℝ)) hcard)
  simpa only [Nat.mul_comm] using hh'

end DirectedFeedback.RawFamily

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
open DFVSGames.Foundations DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity
open DFVSGames.Explicit.MachineOutputContract
variable {D : Nat} (P : Parameters D) (S : BinaryGapReduction P.theta P.theta)
local instance packetLocalityAlphabetNeZero : NeZero S.alphabet :=
  ⟨by have := S.alphabetAtLeastTwo; omega⟩
variable (R : RankParameters P (X S.alphabet)) [NeZero R.N]
variable (C : Nat) (c : Seed S.alphabet P.M P.T R.N → Nat) (hC : 0<C)
variable (hc : ∀ s, (C:ℝ)*mass R.law (8*(D+1)) P.K s=c s)

def Model (x : List Bool) (G : Game (W x) (W x) (E x) (X S.alphabet) (Y S.alphabet))
    (f : E x → X S.alphabet ≃ Y S.alphabet × Bool) : Prop :=
  (∀ e : E x, GameRead.left S.alphabet x e.val=(G.left e).val) ∧
  (∀ e : E x, GameRead.right S.alphabet x e.val=(G.right e).val) ∧
  (∀ e : E x, GameRead.fiber S.alphabet x e.val=f e) ∧
  G.edgeLaw=uniform (E x) ∧ (∀ e a, (f e a).1=G.project e a)

lemma encoded_model (I : Instance S.alphabet)
    (p : (U : Type) → [Fintype U] → (E : Type) → [Fintype E] →
      Game U U E (X S.alphabet) (Y S.alphabet) → Prop)
    (hp : p _ _ (FullGame.game I)) :
    ∃ (G : Game (W (gameBits I)) (W (gameBits I)) (E (gameBits I)) (X S.alphabet) (Y S.alphabet))
      (f : E (gameBits I) → X S.alphabet ≃ Y S.alphabet × Bool),
      Model P S (gameBits I) G f ∧ p _ _ G := by
  have aux (n m : Nat) [Nonempty (Fin m)] (hn : n=I.vertices)
      (hm : m=I.constraints.length) :
      ∃ (G : Game (Fin n) (Fin n) (Fin m) (X S.alphabet) (Y S.alphabet))
        (f : Fin m → X S.alphabet ≃ Y S.alphabet × Bool),
        ((∀ e, GameRead.left S.alphabet (gameBits I) e.val=(G.left e).val) ∧
        (∀ e, GameRead.right S.alphabet (gameBits I) e.val=(G.right e).val) ∧
        (∀ e, GameRead.fiber S.alphabet (gameBits I) e.val=f e) ∧
        G.edgeLaw=uniform (Fin m) ∧ (∀ e a, (f e a).1=G.project e a)) ∧ p _ _ G := by
    subst n m
    refine ⟨FullGame.game I,FullGame.fiber I,?_,hp⟩
    exact ⟨GameRead.left_encoded S.alphabet I,GameRead.right_encoded S.alphabet I,
      GameRead.fiber_encoded S.alphabet I,rfl,FullGame.fiber_project I⟩
  exact aux _ _ (GameRead.n_encoded _ _) (GameRead.m_encoded _ _)

include hc in
theorem encoded_yes (input : List Bool) (h : DFVSGames.BinaryLanguage.language input) :
    ((family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits (S.construct input))).graph.dfvs ≤
    ((family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits (S.construct input))).k := by
  obtain ⟨G,f,⟨hl,hr,hf,hE,hproj⟩,a,b,hab⟩ := encoded_model P S (S.construct input)
    (fun _ _ _ _ G => ∃ a b, 1-(P.theta:ℝ)≤G.score a b) (FullGame.completeness S input h)
  exact completeness P R C c hC hc _ G f hl hr hf hE hproj a b hab

include hc in
theorem encoded_no (A : ℝ) (hA : 4*A≤D) (input : List Bool)
    (h : ¬DFVSGames.BinaryLanguage.language input) :
    A*((family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits (S.construct input))).k <
    (((family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits (S.construct input))).graph.dfvs:ℝ) := by
  obtain ⟨G,f,⟨hl,hr,hf,hE,hproj⟩,hg⟩ := encoded_model P S (S.construct input)
    (fun _ _ _ _ G => G.Sound P.theta) (FullGame.soundness S input h)
  have hh := soundness P R C c hC hc _ G f hl hr hf hE hproj hg
  apply lt_of_le_of_lt _ hh
  change A*((4*scale P.T C (gameBits (S.construct input)):Nat):ℝ)≤_
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg (α:=ℝ) (scale P.T C (gameBits (S.construct input))))]

end DirectedFeedback.RawFamily

end
end

end OAI
