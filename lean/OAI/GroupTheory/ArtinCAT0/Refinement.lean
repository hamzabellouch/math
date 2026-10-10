import OAI.GroupTheory.ArtinCAT0.SectorMetric

namespace OAI

namespace ArtinCAT0.WordDiagram
open Relation

abbrev Side := Word × Bool

def inverseWord (w : Word) : Word := FreeMonoid.ofList (inverseLetters w.toList)
def sideWord (s : Side) : Word := if s.2 then inverseWord s.1 else s.1
def sideFlip (s : Side) : Side := (s.1,!s.2)
noncomputable def sideFull (g : TriangleGroup) (s : Side) (K : ℕ) : List TriangleGroup :=
  if s.2 then (fullSide (g*(eval s.1)⁻¹) s.1 K).reverse else fullSide g s.1 K

@[simp] lemma eval_inverseWord (w : Word) : eval (inverseWord w) = (eval w)⁻¹ :=
  eval_inverseLetters w.toList

@[simp] lemma eval_sideFlip (s : Side) : eval (sideWord (sideFlip s)) = (eval (sideWord s))⁻¹ := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideWord,sideFlip]

lemma sideFull_reverse (g : TriangleGroup) (s : Side) (K : ℕ) :
    (sideFull g s K).reverse = sideFull (g*eval (sideWord s)) (sideFlip s) K := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,sideFlip,sideWord,mul_assoc]

lemma sideFull_length (g : TriangleGroup) (s : Side) (K : ℕ) (h : s.1.toList.length+1 ≤ K) :
    (sideFull g s K).length = K+1 := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,fullSide_length _ _ _ h]

lemma sideFull_contract (g : TriangleGroup) (s : Side) (K : ℕ) (h : s.1.toList.length+2 ≤ K) :
    ReflTransGen PathStep (sideFull g s K).dropLast (walk g (sideWord s).toList) := by
  rcases s with ⟨w,b⟩
  cases b
  · exact fullSide_trim_forward g w K h
  · simpa [sideWord,inverseWord,sideFull,mul_assoc] using
      fullSide_trim_reverse (g*(eval w)⁻¹) w K

lemma fullSide_head (g : TriangleGroup) (w : Word) (K : ℕ) :
    (fullSide g w K).head? = some g := by simp [fullSide]

lemma fullSide_last (g : TriangleGroup) (w : Word) (K : ℕ) (h : w.toList.length+2 ≤ K) :
    (fullSide g w K).getLast? = some (g*eval w) := by
  have hk : K-(w.toList.length+1) = (K-(w.toList.length+2))+1 := by omega
  simp only [fullSide,hk,List.replicate_succ',← List.append_assoc,List.getLast?_concat]

lemma sideFull_head (g : TriangleGroup) (s : Side) (K : ℕ) (h : s.1.toList.length+2 ≤ K) :
    (sideFull g s K).head? = some g := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,fullSide_head,fullSide_last _ _ _ h,mul_assoc]

lemma sideFull_last (g : TriangleGroup) (s : Side) (K : ℕ) (h : s.1.toList.length+2 ≤ K) :
    (sideFull g s K).getLast? = some (g*eval (sideWord s)) := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,sideWord,fullSide_head,fullSide_last _ _ _ h]

def startLabel (s : Fin 3 → Side) (i : Fin 3) : TriangleGroup :=
  if i = 0 then 1 else if i = 1 then eval (sideWord (s 0))
    else eval (sideWord (s 0))*eval (sideWord (s 1))

def closedSides (s : Fin 3 → Side) : Prop :=
  eval (sideWord (s 0))*eval (sideWord (s 1))*eval (sideWord (s 2)) = 1

lemma startLabel_next (s : Fin 3 → Side) (h : closedSides s) (i : Fin 3) :
    startLabel s i * eval (sideWord (s i)) = startLabel s (i+1) := by
  fin_cases i <;> simp [startLabel,show (2 : Fin 3) ≠ 1 by decide,closedSides] at *
  exact h

noncomputable def sideBoundary (s : Fin 3 → Side) (K : ℕ) : List TriangleGroup :=
  (sideFull (startLabel s 0) (s 0) K).dropLast ++
  (sideFull (startLabel s 1) (s 1) K).dropLast ++
  (sideFull (startLabel s 2) (s 2) K).dropLast

lemma sideBoundary_contract (s : Fin 3 → Side) (K : ℕ) (h : ∀ i, (s i).1.toList.length+2 ≤ K) :
    ReflTransGen PathStep (sideBoundary s K)
      (walk 1 (sideWord (s 0)*sideWord (s 1)*sideWord (s 2)).toList) := by
  let p (i : Fin 3) := (sideFull (startLabel s i) (s i) K).dropLast
  let q (i : Fin 3) := walk (startLabel s i) (sideWord (s i)).toList
  have hh i : ReflTransGen PathStep (p i) (q i) := sideFull_contract _ _ _ (h i)
  have h0 := deletions_context (hh 0) [] (p 1++p 2)
  have h1 := deletions_context (hh 1) (q 0) (p 2)
  have h2 := deletions_context (hh 2) (q 0++q 1) []
  have h3 := deletions_context (walk_join 1 (sideWord (s 0)).toList (sideWord (s 1)).toList)
    [] (q 2)
  have h4 := walk_join 1 (sideWord (s 0)*sideWord (s 1)).toList (sideWord (s 2)).toList
  have h01 := h0.trans (by simpa [List.append_assoc] using h1)
  have h012 := h01.trans (by simpa [List.append_assoc] using h2)
  have h0123 := h012.trans (by simpa [q,startLabel,List.append_assoc] using h3)
  simpa [sideBoundary,p,q,startLabel,List.append_assoc,mul_assoc] using h0123.trans
    (by simpa [q,startLabel,mul_assoc] using h4)

lemma sideBoundary_length (s : Fin 3 → Side) (K : ℕ) (h : ∀ i, (s i).1.toList.length+1 ≤ K) :
    (sideBoundary s K).length = 3*K := by
  simp only [sideBoundary,List.length_append,List.length_dropLast,sideFull_length _ _ _ (h _)]
  omega

lemma path_grid_pos {p q : List TriangleGroup} (h : PathHomotopy p q) (g : TriangleGroup) :
    ∃ B : ℕ, ∀ (N : ℕ) [NeZero N], B < N → GoodPath g p →
      ReflTransGen Strip (padded g p : Row N) (padded g q) := by
  obtain ⟨B,hB⟩ := path_grid h g
  refine ⟨B,?_⟩
  intro N hN hBN hp
  cases N with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ N => exact hB N (by omega) hp

/-- A finite collection of triangular loop types admits one common boundary
width and one common disk height. The boundary parametrizations reverse
literally, rather than merely up to homotopy. -/
theorem finite_template_fillers {I : Type*} [Fintype I] (s : I → Fin 3 → Side)
    (hs : ∀ i, closedSides (s i)) :
    ∃ K H : ℕ, ∃ hK : 0 < K, letI : NeZero (3*K) := ⟨by omega⟩;
      (∀ i j, (s i j).1.toList.length+2 ≤ K) ∧
      ∃ v : I → GridDisk.Vertex H (3*K) → TriangleGroup,
      (∀ i j, v i (Sum.inl (Fin.last (H+1),j)) = (sideBoundary (s i) K).getD j.val 1) ∧
      (∀ i a, ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v i ((GridDisk.patch H (3*K)).tail (a,k))) := by
  classical
  have hW i : eval (sideWord (s i 0)*sideWord (s i 1)*sideWord (s i 2)) = 1 := by
    simpa only [map_mul,closedSides] using hs i
  choose B hB using fun i => path_grid_pos (null_path _ (hW i) 1) 1
  let K := 1 + (Finset.univ.sup B) +
    (Finset.univ.sup fun i : I => Finset.univ.sup fun j : Fin 3 => (s i j).1.toList.length+2)
  have hK : 0 < K := by dsimp [K]; omega
  let : NeZero (3*K) := ⟨by omega⟩
  have hbound (i : I) (j : Fin 3) : (s i j).1.toList.length+2 ≤ K := by
    have h1 := Finset.le_sup (f := fun j : Fin 3 => (s i j).1.toList.length+2) (Finset.mem_univ j)
    have h2 := Finset.le_sup (f := fun i : I => Finset.univ.sup fun j : Fin 3 =>
      (s i j).1.toList.length+2) (Finset.mem_univ i)
    dsimp only [K]
    omega
  have hrow (i : I) : ReflTransGen Strip (padded 1 (sideBoundary (s i) K) : Row (3*K)) (fun _ => 1) := by
    have hlen := sideBoundary_length (s i) K (fun j => by have := hbound i j; omega)
    have hc := sideBoundary_contract (s i) K (hbound i)
    have hwgood := walk_good 1 _ (hW i)
    have hpGood := (homotopy_good (deletions_homotopy hc) 1).2 hwgood
    have hd := deletions_grid hc hpGood (by omega : (sideBoundary (s i) K).length ≤ 3*K)
    have hi := Finset.le_sup (f := B) (Finset.mem_univ i)
    have hb : B i < 3*K := by dsimp only [K]; omega
    have ht := hB i (3*K) hb hwgood
    rw [pad_singleton] at ht
    exact hd.trans ht
  choose L hL using fun i => fill_row_tall 1 (padded 1 (sideBoundary (s i) K)) (hrow i)
  let H := Finset.univ.sup L
  choose v hv using fun i => hL i H (Finset.le_sup (Finset.mem_univ i))
  exact ⟨K,H,hK,hbound,v,fun i => (hv i).1,fun i => (hv i).2⟩

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram

lemma getD_dropLast {α : Type*} (l : List α) (d : α) (n : ℕ) (h : n < l.length-1) :
    l.dropLast.getD n d = l.getD n d := by
  rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by omega)]
  simp

lemma sideBoundary_get_interior (s : Fin 3 → Side)
    (K : ℕ) [NeZero K] (h : ∀ i, (s i).1.toList.length+2 ≤ K)
    (i : Fin 3) (j : ℕ) (hj : j<K) :
    (sideBoundary s K).getD (i.val*K+j) 1 =
      (sideFull (startLabel s i) (s i) K).getD j 1 := by
  have hlen (i : Fin 3) : (sideFull (startLabel s i) (s i) K).length = K+1 :=
    sideFull_length _ _ _ (by have := h i; omega)
  have hdlen (i : Fin 3) : ((sideFull (startLabel s i) (s i) K).dropLast).length = K := by
    rw [List.length_dropLast,hlen]; omega
  fin_cases i
  · change (sideBoundary s K).getD (0*K+j) 1 = _
    simp only [zero_mul,zero_add]
    rw [sideBoundary,getD_append_formula,List.length_append,hdlen,hdlen,ite_eq_left (by omega),
      getD_append_formula,hdlen,ite_eq_left hj]
    exact getD_dropLast _ _ _ (by rw [hlen]; omega)
  · change (sideBoundary s K).getD (1*K+j) 1 = _
    simp only [one_mul]
    rw [sideBoundary,getD_append_formula,List.length_append,hdlen,hdlen,ite_eq_left (by omega),
      getD_append_formula,hdlen,ite_eq_right (by omega)]
    rw [show K+j-K=j by omega,getD_dropLast _ _ _ (by rw [hlen]; omega)]
    congr 4
  · change (sideBoundary s K).getD (2*K+j) 1 = _
    rw [sideBoundary,getD_append_formula,List.length_append,hdlen,hdlen,ite_eq_right (by omega)]
    rw [show 2*K+j-(K+K)=j by omega]
    exact getD_dropLast _ _ _ (by rw [hlen]; omega)

lemma sideBoundary_get (s : Fin 3 → Side) (hs : closedSides s)
    (K : ℕ) [NeZero K] (h : ∀ i, (s i).1.toList.length+2 ≤ K)
    (i : Fin 3) (j : Fin (K+1)) :
    (sideBoundary s K).getD (GridDisk.sideIndex K i j).val 1 =
      (sideFull (startLabel s i) (s i) K).getD j.val 1 := by
  have hlen (i : Fin 3) : (sideFull (startLabel s i) (s i) K).length = K+1 :=
    sideFull_length _ _ _ (by have := h i; omega)
  by_cases hj : j.val < K
  · have hm : i.val*K+j.val < 3*K := by
      have hi : i.val*K ≤ 2*K := Nat.mul_le_mul_right K (by omega)
      omega
    change (sideBoundary s K).getD ((i.val*K+j.val)%(3*K)) 1 = _
    rw [Nat.mod_eq_of_lt hm]
    exact sideBoundary_get_interior s K h i j.val hj
  · have he : j = Fin.last K := by apply Fin.ext; simp; omega
    subst j
    have hg i : (sideFull (startLabel s i) (s i) K).getD K 1 = startLabel s (i+1) := by
      rw [← startLabel_next s hs i]
      have hl := sideFull_last (startLabel s i) (s i) K (h i)
      rw [List.getLast?_eq_getElem?,hlen] at hl
      change ((sideFull (startLabel s i) (s i) K)[K]?).getD 1 = _
      simpa only [Nat.add_sub_cancel_right,Option.getD_some] using
        congrArg (fun t : Option TriangleGroup => t.getD 1) hl
    simp only [Fin.val_last,hg]
    have he : GridDisk.sideIndex K i (Fin.last K) = GridDisk.sideIndex K (i+1) 0 := by
      have he := GridDisk.sidePoint_ends (H:=0) K i
      exact congrArg Prod.snd (Sum.inl.inj he)
    rw [he]
    have hm : (i+1).val*K < 3*K := Nat.mul_lt_mul_of_pos_right (i+1).isLt (NeZero.pos K)
    change (sideBoundary s K).getD (((i+1).val*K+0)%(3*K)) 1 = _
    rw [Nat.add_zero,Nat.mod_eq_of_lt hm]
    have hi := sideBoundary_get_interior s K h (i+1) 0 (NeZero.pos K)
    simp only [Nat.add_zero] at hi
    rw [hi]
    rw [List.getD,← List.head?_eq_getElem?]
    simp only [sideFull_head _ _ _ (h _),Option.getD_some]

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram

lemma walk_translate (a g : TriangleGroup) (w : List Letter) :
    walk (a*g) w = (walk g w).map (a*·) := by
  induction w generalizing g with
  | nil => rfl
  | cons s w ih => simp only [walk,List.map_cons,mul_assoc,ih]

lemma fullSide_translate (a g : TriangleGroup) (w : Word) (K : ℕ) :
    fullSide (a*g) w K = (fullSide g w K).map (a*·) := by
  simp [fullSide,walk_translate,mul_assoc]

lemma sideFull_translate (a g : TriangleGroup) (s : Side) (K : ℕ) :
    sideFull (a*g) s K = (sideFull g s K).map (a*·) := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,fullSide_translate,mul_assoc,List.map_reverse]

lemma sideFull_getTranslate (a g : TriangleGroup) (s : Side) (K : ℕ)
    (h : s.1.toList.length+1 ≤ K) (j : Fin (K+1)) :
    (sideFull (a*g) s K).getD j.val 1 = a*(sideFull g s K).getD j.val 1 := by
  rw [sideFull_translate]
  have hl : j.val < (sideFull g s K).length := by rw [sideFull_length _ _ _ h]; exact j.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hl),List.getD_eq_getElem _ _ hl]
  simp

lemma sideFull_getReverse (g : TriangleGroup) (s : Side) (K : ℕ)
    (h : s.1.toList.length+1 ≤ K) (j : Fin (K+1)) :
    (sideFull (g*eval (sideWord s)) (sideFlip s) K).getD j.rev.val 1 =
      (sideFull g s K).getD j.val 1 := by
  rw [← sideFull_reverse,List.getD_reverse j.rev.val (by
    rw [sideFull_length _ _ _ h]; exact j.rev.isLt),sideFull_length _ _ _ h]
  congr 1
  simp only [Fin.val_rev]
  omega

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open TriangleMesh

lemma TargetLegal_translate (b : TriangleGroup) {v : Fin 3 → TriangleGroup}
    (h : ∃ t : TargetTriangle, ∀ k, ∃ j, t.vertex j = v k) :
    ∃ t : TargetTriangle, ∀ k, ∃ j, t.vertex j = b*v k := by
  obtain ⟨t,ht⟩ := h
  refine ⟨⟨b*t.base,t.block,t.rel⟩,?_⟩
  intro k
  obtain ⟨j,hj⟩ := ht k
  refine ⟨j,?_⟩
  simpa only [TargetTriangle.vertex,mul_assoc] using congrArg (b*·) hj

section Refinement
variable {I F V : Type*} (M : TriangleMesh F V)
  (s : I → Fin 3 → Side) (hs : ∀ i, closedSides (s i))
  (K H : ℕ) [NeZero K]
  (hK : ∀ i j, (s i j).1.toList.length+2 ≤ K)
  (v : I → GridDisk.Vertex H (3*K) → TriangleGroup)
  (hv : ∀ i j, v i (Sum.inl (Fin.last (H+1),j)) = (sideBoundary (s i) K).getD j.val 1)
  (τ : F → I) (b : F → TriangleGroup) (z : V → TriangleGroup)
  (hb : ∀ f i, b f * startLabel (s (τ f)) i = z (M.tail (f,i)))
  (hm : ∀ f i, s (τ (M.mate (f,i)).1) (M.mate (f,i)).2 = sideFlip (s (τ f) i))
include hs hK hv hb hm

lemma template_seam (f : F) (i : Fin 3) (j : Fin (K+1)) :
    b f * v (τ f) ((GridDisk.sides H K).point (i,j)) =
      b (M.mate (f,i)).1 * v (τ (M.mate (f,i)).1)
        ((GridDisk.sides H K).point ((M.mate (f,i)).2,j.rev)) := by
  change b f * v (τ f) (Sum.inl (Fin.last (H+1),GridDisk.sideIndex K i j)) =
    b (M.mate (f,i)).1 * v (τ (M.mate (f,i)).1)
      (Sum.inl (Fin.last (H+1),GridDisk.sideIndex K (M.mate (f,i)).2 j.rev))
  rw [hv,hv,sideBoundary_get _ (hs _) K (hK _),sideBoundary_get _ (hs _) K (hK _),
    ← sideFull_getTranslate _ _ _ K (by have := hK (τ f) i; omega),
    ← sideFull_getTranslate _ _ _ K (by have := hK (τ (M.mate (f,i)).1) (M.mate (f,i)).2; omega),
    hb,hb,hm,M.tail_mate]
  have he : z (M.tail (f,i+1)) = z (M.tail (f,i))*eval (sideWord (s (τ f) i)) := by
    rw [← hb f (i+1),← hb f i,mul_assoc,startLabel_next _ (hs _)]
  rw [he]
  exact (sideFull_getReverse _ _ K (by have := hK (τ f) i; omega) j).symm

noncomputable def refinedLabels :
    Replacement.Vertex M (GridDisk.patch H (3*K)) (GridDisk.sides H K) → TriangleGroup :=
  Quot.lift (fun p : F × GridDisk.Vertex H (3*K) => b p.1*v (τ p.1) p.2) (by
    intro u w huw
    obtain ⟨f,i,j,rfl,rfl⟩ := huw
    exact template_seam M s hs K H hK v hv τ b z hb hm f i j)

lemma refinedLabels_tail (f : F) (a : GridDisk.Face H (3*K)) (i : Fin 3) :
    refinedLabels M s hs K H hK v hv τ b z hb hm
      ((Replacement.mesh M (GridDisk.patch H (3*K)) (GridDisk.sides H K)).tail ((f,a),i)) =
      b f*v (τ f) ((GridDisk.patch H (3*K)).tail (a,i)) := rfl

lemma refinedLabels_legal
    (hl : ∀ i a, ∃ t : TargetTriangle, ∀ k, ∃ j,
      t.vertex j = v i ((GridDisk.patch H (3*K)).tail (a,k)))
    (f : F × GridDisk.Face H (3*K)) :
    ∃ t : TargetTriangle, ∀ k, ∃ j, t.vertex j =
      refinedLabels M s hs K H hK v hv τ b z hb hm
        ((Replacement.mesh M (GridDisk.patch H (3*K)) (GridDisk.sides H K)).tail (f,k)) := by
  exact TargetLegal_translate (b f.1) (hl (τ f.1) f.2)

end Refinement
end ArtinCAT0.WordDiagram

namespace ArtinCAT0

@[simp] lemma mirrorLinear_one : mirrorLinear 1 = 1 := by simp [mirrorLinear]
@[simp] lemma mirrorLinear_inv (g : TriangleGroup) : mirrorLinear g⁻¹ = (mirrorLinear g)⁻¹ := by
  simp [mirrorLinear]
@[simp] lemma mirrorLinear_zpow (g : TriangleGroup) (n : ℤ) :
    mirrorLinear (g^n) = mirrorLinear g ^ n := by
  exact map_zpow (SemidirectProduct.rightHom.comp mirrorRepresentation) g n

lemma mirrorVector_pure_mul {g : TriangleGroup} (hg : mirrorLinear g = 1)
    (h : TriangleGroup) (d : Mirror) :
    mirrorVector (g*h) d = mirrorVector g d + mirrorVector h d := by
  rw [mirrorVector_mul,hg]
  rfl

lemma mirrorVector_pure_pow {g : TriangleGroup} (hg : mirrorLinear g = 1)
    (n : ℕ) (d : Mirror) : mirrorVector (g^n) d = (n:ℝ)*mirrorVector g d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mirrorVector_pure_mul hg,ih]
    push_cast
    ring

lemma mirrorVector_pure_zpow {g : TriangleGroup} (hg : mirrorLinear g = 1)
    (n : ℤ) (d : Mirror) : mirrorVector (g^n) d = (n:ℝ)*mirrorVector g d := by
  cases n with
  | ofNat n => simpa using mirrorVector_pure_pow hg n d
  | negSucc n =>
    rw [zpow_negSucc,mirrorVector_inv]
    have hpow : mirrorLinear (g^(n+1)) = 1 := by
      have h := mirrorLinear_zpow g (n+1)
      norm_cast at h
      rw [h,hg,one_pow]
    rw [hpow]
    simp only [Equiv.Perm.one_apply,mirrorVector_pure_pow hg,Int.cast_negSucc]
    ring

noncomputable def mirrorPlane (g : TriangleGroup) : ℝ × ℝ :=
  ((mirrorVector g (sideMirror 0)-mirrorVector g (extraMirror 0))/2,
    mirrorVector g (extraMirror 0)/2)

@[simp] lemma mirrorPlane_one : mirrorPlane 1 = (0,0) := by simp [mirrorPlane]

lemma mirrorPlane_pure_mul {g : TriangleGroup} (hg : mirrorLinear g = 1) (h : TriangleGroup) :
    mirrorPlane (g*h) = ( (mirrorPlane g).1+(mirrorPlane h).1,
      (mirrorPlane g).2+(mirrorPlane h).2) := by
  ext <;> simp only [mirrorPlane,mirrorVector_pure_mul hg] <;> ring

lemma mirrorPlane_pure_zpow {g : TriangleGroup} (hg : mirrorLinear g = 1) (n : ℤ) :
    mirrorPlane (g^n) = ((n:ℝ)*(mirrorPlane g).1,(n:ℝ)*(mirrorPlane g).2) := by
  ext <;> simp only [mirrorPlane,mirrorVector_pure_zpow hg] <;> ring

lemma mirrorPlane_mul_bound (g h : TriangleGroup) {D : ℝ}
    (hh : ∀ d, |mirrorVector h d| ≤ D) :
    |(mirrorPlane (g*h)).1-(mirrorPlane g).1| ≤ D ∧
    |(mirrorPlane (g*h)).2-(mirrorPlane g).2| ≤ D := by
  have hd : 0 ≤ D := (abs_nonneg _).trans (hh (sideMirror 0))
  constructor
  · change |(mirrorVector (g*h) (sideMirror 0)-mirrorVector (g*h) (extraMirror 0))/2-
      (mirrorVector g (sideMirror 0)-mirrorVector g (extraMirror 0))/2| ≤ D
    rw [mirrorVector_mul,mirrorVector_mul]
    have he (a b c d : ℝ) : (a+b-(c+d))/2-(a-c)/2 = (b-d)/2 := by ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have h1 := hh ((mirrorLinear g).symm (sideMirror 0))
    have h2 := hh ((mirrorLinear g).symm (extraMirror 0))
    exact (abs_sub _ _).trans (by linarith)
  · change |mirrorVector (g*h) (extraMirror 0)/2-mirrorVector g (extraMirror 0)/2| ≤ D
    rw [mirrorVector_mul,add_div,add_sub_cancel_left,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    linarith [hh ((mirrorLinear g).symm (extraMirror 0))]

namespace SixSector

def planeRay (i : Fin 6) : ℝ × ℝ :=
  if i = 0 ∨ i = 5 then (1,0) else if i = 1 then (0,1) else (0,0)

lemma ray_rep_even (i : Fin 3) :
    mirrorRepresentation (triangleGen i^2) =
      ⟨Multiplicative.ofAdd (2 • mirrorBasis (sideMirror i)),1⟩ := by
  rw [map_pow,mirrorRepresentation_gen,mirrorGenerator_sq]

lemma ray_rep_odd (i : Fin 3) :
    mirrorRepresentation (triangleH i^3) =
      ⟨Multiplicative.ofAdd (2 • (mirrorBasis (sideMirror i)+mirrorBasis (extraMirror i)+
        mirrorBasis (sideMirror (i+1)))),1⟩ := by
  rw [triangleH,map_pow,map_mul,mirrorRepresentation_gen,mirrorRepresentation_gen,
    mirrorGenerator_center]

lemma ray_pure (i : Fin 6) : mirrorLinear (ray i) = 1 := by
  have he k : mirrorLinear (triangleGen k^2) = 1 := by
    unfold mirrorLinear; rw [ray_rep_even]
  have ho k : mirrorLinear (triangleH k^3) = 1 := by
    unfold mirrorLinear; rw [ray_rep_odd]
  fin_cases i
  · exact he 0
  · exact ho 0
  · exact he 1
  · exact ho 1
  · exact he 2
  · exact ho 2

lemma ray_plane (i : Fin 6) : mirrorPlane (ray i) = planeRay i := by
  have he (k : Fin 3) (d : Mirror) :
      mirrorVector (triangleGen k^2) d = 2*mirrorBasis (sideMirror k) d := by
    simp [mirrorVector,ray_rep_even,two_smul]
    ring
  have ho (k : Fin 3) (d : Mirror) :
      mirrorVector (triangleH k^3) d =
        2*(mirrorBasis (sideMirror k) d+mirrorBasis (extraMirror k) d+
          mirrorBasis (sideMirror (k+1)) d) := by
    simp [mirrorVector,ray_rep_odd,two_smul]
    ring
  fin_cases i <;> ext <;>
    simp [ray,mirrorPlane,planeRay,he,ho,mirrorBasis,sideMirror,extraMirror]

lemma lattice_plane (i : Fin 6) (L M : ℝ) (p : ℝ × ℝ) :
    mirrorPlane (SectorMetric.lattice (ray i) (ray (i+1)) L M p) =
      ((⌊p.1/L⌋:ℝ)*(planeRay i).1+(⌊p.2/M⌋:ℝ)*(planeRay (i+1)).1,
       (⌊p.1/L⌋:ℝ)*(planeRay i).2+(⌊p.2/M⌋:ℝ)*(planeRay (i+1)).2) := by
  have h : mirrorLinear (ray i ^ ⌊p.1/L⌋) = 1 := by rw [mirrorLinear_zpow,ray_pure,one_zpow]
  rw [SectorMetric.lattice,mirrorPlane_pure_mul h,
    mirrorPlane_pure_zpow (ray_pure i),mirrorPlane_pure_zpow (ray_pure (i+1)),
    ray_plane,ray_plane]

end SixSector
end ArtinCAT0

end OAI
