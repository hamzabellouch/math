import Mathlib

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def ScalarFree {ι : Type*} (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) : Prop :=
  ∀ w : List (ι × A), w ≠ [] →
    w.IsChain (fun x y => x.1 ≠ y.1) →
    (∀ x ∈ w, x.2 ∈ S x.1 ∧ τ x.2 = 0) →
    τ ((w.map Prod.snd).prod) = 0

def FaithfulTracial (τ : A →ₚ[ℂ] ℂ) : Prop :=
  τ 1 = 1 ∧ (∀ x y : A, τ (x * y) = τ (y * x)) ∧
    ∀ x : A, τ (star x * x) = 0 → x = 0

structure FreePartitions (τ : A →ₚ[ℂ] ℂ) (r d : ℕ) where
  S : Fin r → StarSubalgebra ℂ A
  e : Fin r → Fin d → A
  mem : ∀ j a, e j a ∈ S j
  selfadjoint : ∀ j a, star (e j a) = e j a
  mul : ∀ j a b, e j a * e j b = if a = b then e j a else 0
  sum : ∀ j, ∑ a, e j a = 1
  trace : ∀ j a, τ (e j a) = (d : ℂ)⁻¹
  free : ScalarFree τ S

def wordSum {τ : A →ₚ[ℂ] ℂ} {r d : ℕ} (P : FreePartitions τ r d)
    (W : Sym (Fin d) r) : A :=
  ∑ a ∈ (Finset.univ : Finset (Fin r → Fin d)).filter
      (fun a => (List.ofFn a : Multiset (Fin d)) = (W : Multiset (Fin d))),
    ((List.ofFn (fun j => P.e j (a j))).reverse).prod

variable {ι : Type*} {τ : A →ₚ[ℂ] ℂ} {S : ι → StarSubalgebra ℂ A}

def wordValue (w : List (ι × A)) : A := (w.map Prod.snd).prod

def adjointWord (w : List (ι × A)) : List (ι × A) :=
  w.reverse.map (fun x => (x.1, star x.2))

def Reduced (w : List (ι × A)) : Prop :=
  w.IsChain (fun x y => x.1 ≠ y.1) ∧
  ∀ x ∈ w, x.2 ∈ S x.1 ∧ τ x.2 = 0

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem wordValue_nil : wordValue ([] : List (ι × A)) = 1 := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem wordValue_cons (x : ι × A) (w : List (ι × A)) :
    wordValue (x :: w) = x.2 * wordValue w := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem wordValue_append (u v : List (ι × A)) :
    wordValue (u ++ v) = wordValue u * wordValue v := by
  simp [wordValue]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem adjointWord_nil : adjointWord ([] : List (ι × A)) = [] := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem adjointWord_cons (x : ι × A) (w : List (ι × A)) :
    adjointWord (x :: w) = adjointWord w ++ [(x.1, star x.2)] := by
  simp [adjointWord]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem wordValue_adjointWord (w : List (ι × A)) :
    wordValue (adjointWord w) = star (wordValue w) := by
  induction w with
  | nil => simp
  | cons x w ih => simp [ih]

omit [StarOrderedRing A] in
theorem Reduced.tail {x : ι × A} {w : List (ι × A)}
    (h : Reduced (τ := τ) (S := S) (x :: w)) : Reduced (τ := τ) (S := S) w := by
  exact ⟨h.1.tail, fun y hy => h.2 y (List.mem_cons_of_mem x hy)⟩

omit [StarOrderedRing A] in
theorem Reduced.head {x : ι × A} {w : List (ι × A)}
    (h : Reduced (τ := τ) (S := S) (x :: w)) : x.2 ∈ S x.1 ∧ τ x.2 = 0 :=
  h.2 x (by simp)

theorem Reduced.adjointWord {w : List (ι × A)}
    (h : Reduced (τ := τ) (S := S) w) :
    Reduced (τ := τ) (S := S) (adjointWord w) := by
  constructor
  · rw [KKFreeWords.adjointWord, List.isChain_map, List.isChain_reverse]
    exact h.1.imp (fun _ _ hxy => Ne.symm hxy)
  · intro x hx
    simp only [KKFreeWords.adjointWord, List.mem_map, List.mem_reverse] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨hm, hz⟩ := h.2 y hy
    exact ⟨star_mem hm, by simpa [hz] using (map_star τ y.2)⟩

omit [StarOrderedRing A] in
theorem Reduced.trace_zero (hfree : ScalarFree τ S) {w : List (ι × A)}
    (h : Reduced (τ := τ) (S := S) w) (hne : w ≠ []) : τ (wordValue w) = 0 :=
  hfree w hne h.1 h.2

omit [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
theorem chain_iff_indices (w : List (ι × A)) :
    w.IsChain (fun x y => x.1 ≠ y.1) ↔ (w.map Prod.fst).IsChain Ne := by
  rw [List.isChain_map]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem adjointWord_indices (w : List (ι × A)) :
    (adjointWord w).map Prod.fst = (w.map Prod.fst).reverse := by
  simp [adjointWord, List.map_reverse, Function.comp_def]

omit [PartialOrder A] [StarOrderedRing A] in
theorem chain_junction {i : ι} {a b c : A} {u v : List (ι × A)}
    (hu : ((i,a) :: u).IsChain (fun x y => x.1 ≠ y.1))
    (hv : ((i,b) :: v).IsChain (fun x y => x.1 ≠ y.1)) :
    (adjointWord u ++ (i,c) :: v).IsChain (fun x y => x.1 ≠ y.1) := by
  rw [chain_iff_indices, List.map_append, List.map_cons,
    adjointWord_indices, List.isChain_split]
  constructor
  · change ((u.map Prod.fst).reverse ++ [i]).IsChain Ne
    rw [← List.reverse_cons, List.isChain_reverse]
    exact ((chain_iff_indices ((i,a) :: u)).mp hu).imp (fun _ _ hxy => Ne.symm hxy)
  · exact (chain_iff_indices ((i,b) :: v)).mp hv

omit [PartialOrder A] [StarOrderedRing A] in
theorem chain_distinct_junction {i j : ι} {a b : A} {u v : List (ι × A)}
    (hu : ((i,a) :: u).IsChain (fun x y => x.1 ≠ y.1))
    (hv : ((j,b) :: v).IsChain (fun x y => x.1 ≠ y.1)) (hne : i ≠ j) :
    (adjointWord ((i,a) :: u) ++ (j,b) :: v).IsChain
      (fun x y => x.1 ≠ y.1) := by
  simp only [adjointWord_cons, List.append_assoc, List.singleton_append]
  rw [List.isChain_append_cons_cons]
  refine ⟨?_, hne, hv⟩
  have hc := (chain_iff_indices ((i,a) :: u)).mp hu
  rw [chain_iff_indices, List.map_append, adjointWord_indices]
  change ((u.map Prod.fst).reverse ++ [i]).IsChain Ne
  rw [← List.reverse_cons, List.isChain_reverse]
  exact hc.imp (fun _ _ hxy => Ne.symm hxy)

theorem trace_centered_junction (hfree : ScalarFree τ S)
    {i : ι} {a b c : A} {u v : List (ι × A)}
    (hu : Reduced (τ := τ) (S := S) ((i,a) :: u))
    (hv : Reduced (τ := τ) (S := S) ((i,b) :: v))
    (hc : c ∈ S i ∧ τ c = 0) :
    τ (star (wordValue u) * c * wordValue v) = 0 := by
  have hred : Reduced (τ := τ) (S := S) (adjointWord u ++ (i,c) :: v) := by
    refine ⟨chain_junction hu.1 hv.1, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hu.tail.adjointWord.2 x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact hv.tail.2 x hx
  have h := hred.trace_zero hfree (by simp)
  simpa only [wordValue_append, wordValue_adjointWord, wordValue_cons, mul_assoc]
    using h

theorem trace_distinct_junction (hfree : ScalarFree τ S)
    {i j : ι} {a b : A} {u v : List (ι × A)}
    (hu : Reduced (τ := τ) (S := S) ((i,a) :: u))
    (hv : Reduced (τ := τ) (S := S) ((j,b) :: v)) (hne : i ≠ j) :
    τ (star (wordValue ((i,a)::u)) * wordValue ((j,b)::v)) = 0 := by
  have hred : Reduced (τ := τ) (S := S)
      (adjointWord ((i,a)::u) ++ (j,b)::v) := by
    refine ⟨chain_distinct_junction hu.1 hv.1 hne, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hu.adjointWord.2 x hx
    · exact hv.2 x hx
  simpa only [wordValue_append, wordValue_adjointWord] using
    hred.trace_zero hfree (by simp)

theorem trace_same_junction (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    {i : ι} {a b : A} {u v : List (ι × A)}
    (hu : Reduced (τ := τ) (S := S) ((i,a) :: u))
    (hv : Reduced (τ := τ) (S := S) ((i,b) :: v)) :
    τ (star (wordValue ((i,a)::u)) * wordValue ((i,b)::v)) =
      τ (star a * b) * τ (star (wordValue u) * wordValue v) := by
  let z : ℂ := τ (star a * b)
  let c : A := star a * b - z • 1
  have hc : c ∈ S i ∧ τ c = 0 := by
    constructor
    · exact sub_mem (mul_mem (star_mem hu.head.1) hv.head.1)
        ((S i).smul_mem (one_mem _) z)
    · simp [c, z, map_sub, map_smul, hτ]
  have hzero := trace_centered_junction hfree hu hv hc
  have heq : τ (star (wordValue u) * (star a * b) * wordValue v) =
      z * τ (star (wordValue u) * wordValue v) := by
    apply sub_eq_zero.mp
    simpa only [c, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
      map_sub, map_smul, smul_eq_mul] using hzero
  simpa only [wordValue_cons, star_mul, mul_assoc] using heq

theorem trace_reduced_inner [DecidableEq ι] (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    (u v : List (ι × A)) (hu : Reduced (τ := τ) (S := S) u)
    (hv : Reduced (τ := τ) (S := S) v) :
    τ (star (wordValue u) * wordValue v) =
      if u.map Prod.fst = v.map Prod.fst then
        (u.zipWith (fun x y => τ (star x.2 * y.2)) v).prod else 0 := by
  classical
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => simp [hτ]
    | cons y v =>
      simpa using hv.trace_zero hfree (by simp)
  | cons x u ih =>
    cases v with
    | nil =>
      have hz := hu.adjointWord.trace_zero hfree (by simp)
      simpa using hz
    | cons y v =>
      obtain ⟨i,a⟩ := x
      obtain ⟨j,b⟩ := y
      by_cases hij : i = j
      · subst j
        rw [trace_same_junction hfree hτ hu hv, ih v hu.tail hv.tail]
        simp only [List.map_cons, List.cons.injEq, true_and, List.zipWith_cons_cons,
          List.prod_cons]
        split_ifs <;> simp_all
      · rw [trace_distinct_junction hfree hu hv hij]
        simp [hij]

open scoped InnerProductSpace

def gnsVector (τ : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] τ.GNS :=
  UniformSpace.Completion.toComplL.toLinearMap ∘ₗ τ.toPreGNS.toLinearMap

@[simp] theorem gnsVector_inner (x y : A) :
    ⟪gnsVector τ x, gnsVector τ y⟫_ℂ = τ (star x * y) := by
  change ⟪(τ.toPreGNS x : τ.GNS), (τ.toPreGNS y : τ.GNS)⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
  rfl

@[simp] theorem gnsStarAlgHom_vector (x y : A) :
    τ.gnsStarAlgHom x (gnsVector τ y) = gnsVector τ (x * y) := by
  change τ.gnsNonUnitalStarAlgHom x (τ.toPreGNS y : τ.GNS) =
    (τ.toPreGNS (x * y) : τ.GNS)
  simp

theorem gnsVector_injective (hfaith : ∀ x : A, τ (star x * x) = 0 → x = 0) :
    Function.Injective (gnsVector τ) := by
  intro x y hxy
  have hz : gnsVector τ (x - y) = 0 := by simpa only [map_sub, sub_eq_zero] using hxy
  have hc : τ (star (x-y) * (x-y)) = 0 := by
    rw [← gnsVector_inner, hz, inner_zero_left]
  exact sub_eq_zero.mp (hfaith _ hc)

theorem gnsStarAlgHom_injective
    (hfaith : ∀ x : A, τ (star x * x) = 0 → x = 0) :
    Function.Injective τ.gnsStarAlgHom := by
  intro x y hxy
  apply gnsVector_injective hfaith
  have h := congrArg (fun T : τ.GNS →L[ℂ] τ.GNS => T (gnsVector τ 1)) hxy
  simpa only [gnsStarAlgHom_vector, mul_one] using h

theorem gnsStarAlgHom_norm
    (hfaith : ∀ x : A, τ (star x * x) = 0 → x = 0) (x : A) :
    ‖τ.gnsStarAlgHom x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map τ.gnsStarAlgHom (gnsStarAlgHom_injective hfaith) x

theorem gnsVector_word_inner [DecidableEq ι] (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    (u v : List (ι × A)) (hu : Reduced (τ := τ) (S := S) u)
    (hv : Reduced (τ := τ) (S := S) v) :
    ⟪gnsVector τ (wordValue u), gnsVector τ (wordValue v)⟫_ℂ =
      if u.map Prod.fst = v.map Prod.fst then
        (u.zipWith (fun x y => τ (star x.2 * y.2)) v).prod else 0 := by
  rw [gnsVector_inner]
  exact trace_reduced_inner hfree hτ u v hu hv

def HeadOutside (i : ι) (w : List (ι × A)) : Prop :=
  (w.map Prod.fst).head? ≠ some i

omit [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem headOutside_nil (i : ι) : HeadOutside i ([] : List (ι × A)) := by
  simp [HeadOutside]

omit [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem headOutside_cons (i : ι) (x : ι × A) (w : List (ι × A)) :
    HeadOutside i (x :: w) ↔ x.1 ≠ i := by simp [HeadOutside]

omit [StarOrderedRing A] in
theorem Reduced.cons_of_headOutside {i : ι} {a : A} {w : List (ι × A)}
    (hw : Reduced (τ := τ) (S := S) w) (ho : HeadOutside i w)
    (ha : a ∈ S i ∧ τ a = 0) : Reduced (τ := τ) (S := S) ((i,a) :: w) := by
  constructor
  · cases w with
    | nil => simp
    | cons x w =>
      rw [List.isChain_cons_cons]
      exact ⟨Ne.symm ((headOutside_cons i x w).mp ho), hw.1⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hw.2 x hx

def tailWords (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) (i : ι) : Set τ.GNS :=
  {ξ | ∃ w, Reduced (τ := τ) (S := S) w ∧ HeadOutside i w ∧
    ξ = gnsVector τ (wordValue w)}

def tailSpace (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) (i : ι) :
    Submodule ℂ τ.GNS := (Submodule.span ℂ (tailWords τ S i)).topologicalClosure

theorem inner_create_span (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    {i : ι} {a b : A} (ha : a ∈ S i ∧ τ a = 0) (hb : b ∈ S i ∧ τ b = 0)
    {ξ η : τ.GNS} (hξ : ξ ∈ Submodule.span ℂ (tailWords τ S i))
    (hη : η ∈ Submodule.span ℂ (tailWords τ S i)) :
    ⟪τ.gnsStarAlgHom a ξ, τ.gnsStarAlgHom b η⟫_ℂ =
      τ (star a * b) * ⟪ξ, η⟫_ℂ := by
  refine Submodule.span_induction₂ (p := fun ξ η _ _ =>
    ⟪τ.gnsStarAlgHom a ξ, τ.gnsStarAlgHom b η⟫_ℂ =
      τ (star a * b) * ⟪ξ, η⟫_ℂ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hξ hη
  · intro ξ η hξ hη
    obtain ⟨u, hu, hou, rfl⟩ := hξ
    obtain ⟨v, hv, hov, rfl⟩ := hη
    simp only [gnsStarAlgHom_vector, gnsVector_inner]
    exact trace_same_junction hfree hτ (hu.cons_of_headOutside hou ha)
      (hv.cons_of_headOutside hov hb)
  · intro y hy; simp
  · intro x hx; simp
  · intro x y z hx hy hz h₁ h₂
    simp only [map_add, inner_add_left, h₁, h₂, mul_add]
  · intro x y z hx hy hz h₁ h₂
    simp only [map_add, inner_add_right, h₁, h₂, mul_add]
  · intro z x y hx hy h
    simp only [map_smul, inner_smul_left, h]
    ring
  · intro z x y hx hy h
    simp only [map_smul, inner_smul_right, h]
    ring

theorem inner_create (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    {i : ι} {a b : A} (ha : a ∈ S i ∧ τ a = 0) (hb : b ∈ S i ∧ τ b = 0)
    {ξ η : τ.GNS} (hξ : ξ ∈ tailSpace τ S i) (hη : η ∈ tailSpace τ S i) :
    ⟪τ.gnsStarAlgHom a ξ, τ.gnsStarAlgHom b η⟫_ℂ =
      τ (star a * b) * ⟪ξ, η⟫_ℂ := by
  have hleft : ∀ y ∈ Submodule.span ℂ (tailWords τ S i),
      ∀ x ∈ tailSpace τ S i,
        ⟪τ.gnsStarAlgHom a x, τ.gnsStarAlgHom b y⟫_ℂ =
          τ (star a * b) * ⟪x,y⟫_ℂ := by
    intro y hy x hx
    apply (closure_minimal (t := {z | ⟪τ.gnsStarAlgHom a z, τ.gnsStarAlgHom b y⟫_ℂ =
      τ (star a * b) * ⟪z,y⟫_ℂ}) ?_ ?_) hx
    · intro z hz; exact inner_create_span hfree hτ ha hb hz hy
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  apply (closure_minimal (t := {z | ⟪τ.gnsStarAlgHom a ξ, τ.gnsStarAlgHom b z⟫_ℂ =
    τ (star a * b) * ⟪ξ,z⟫_ℂ}) ?_ ?_) hη
  · intro z hz; exact hleft z hz ξ hξ
  · exact isClosed_eq (by fun_prop) (by fun_prop)

theorem closedSpan_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (s t : Set E)
    (h : ∀ x ∈ s, ∀ y ∈ t, ⟪x,y⟫_ℂ = 0) :
    (Submodule.span ℂ s).topologicalClosure ≤
      (Submodule.span ℂ t).topologicalClosureᗮ := by
  rw [Submodule.orthogonal_closure]
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_orthogonal _)
  refine Submodule.span_le.mpr ?_
  intro x hx
  change x ∈ (Submodule.span ℂ t)ᗮ
  rw [Submodule.mem_orthogonal']
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact h x hx y hy
  | zero => simp
  | add y z hy hz iy iz => simp [inner_add_right, iy, iz]
  | smul c y hy iy => simp [inner_smul_right, iy]

def reducedWords (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) : Set τ.GNS :=
  {ξ | ∃ w, Reduced (τ := τ) (S := S) w ∧ ξ = gnsVector τ (wordValue w)}

def reducedSpace (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) : Submodule ℂ τ.GNS :=
  (Submodule.span ℂ (reducedWords τ S)).topologicalClosure

def headWords (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) (i : ι) : Set τ.GNS :=
  {ξ | ∃ w, Reduced (τ := τ) (S := S) w ∧ (w.map Prod.fst).head? = some i ∧
    ξ = gnsVector τ (wordValue w)}

def headSpace (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) (i : ι) : Submodule ℂ τ.GNS :=
  (Submodule.span ℂ (headWords τ S i)).topologicalClosure

instance reducedSpace_complete : CompleteSpace (reducedSpace τ S) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

instance headSpace_complete (i : ι) : CompleteSpace (headSpace τ S i) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

instance tailSpace_complete (i : ι) : CompleteSpace (tailSpace τ S i) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem headSpace_orthogonal_tail (hfree : ScalarFree τ S) (hτ : τ 1 = 1) (i : ι) :
    headSpace τ S i ≤ (tailSpace τ S i)ᗮ := by
  classical
  apply closedSpan_orthogonal
  rintro x ⟨u, hu, hou, rfl⟩ y ⟨v, hv, hov, rfl⟩
  have hne : u.map Prod.fst ≠ v.map Prod.fst := by
    intro he
    exact hov (he ▸ hou)
  simp only [gnsVector_word_inner hfree hτ u v hu hv, ite_eq_right hne]

theorem headSpace_le_tailSpace {i j : ι} (hij : i ≠ j) :
    headSpace τ S i ≤ tailSpace τ S j := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro x ⟨w, hw, ho, hx⟩
  exact ⟨w, hw, by simpa [HeadOutside, ho] using hij, hx⟩

theorem headSpace_le_reducedSpace (i : ι) : headSpace τ S i ≤ reducedSpace τ S := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro x ⟨w, hw, ho, hx⟩
  exact ⟨w, hw, hx⟩

theorem tailSpace_le_reducedSpace (i : ι) : tailSpace τ S i ≤ reducedSpace τ S := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro x ⟨w, hw, ho, hx⟩
  exact ⟨w, hw, hx⟩

theorem reducedVector_mem {w : List (ι × A)} (hw : Reduced (τ := τ) (S := S) w) :
    gnsVector τ (wordValue w) ∈ reducedSpace τ S :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, hw, rfl⟩)

theorem vacuum_mem_reducedSpace : gnsVector τ 1 ∈ reducedSpace τ S := by
  apply reducedVector_mem (w := [])
  exact ⟨by simp, by simp⟩

theorem headVector_mem {w : List (ι × A)} (hw : Reduced (τ := τ) (S := S) w)
    {i : ι} (ho : (w.map Prod.fst).head? = some i) :
    gnsVector τ (wordValue w) ∈ headSpace τ S i :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, hw, ho, rfl⟩)

theorem tailVector_mem {w : List (ι × A)} (hw : Reduced (τ := τ) (S := S) w)
    {i : ι} (ho : HeadOutside i w) :
    gnsVector τ (wordValue w) ∈ tailSpace τ S i :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, hw, ho, rfl⟩)

theorem head_add_tail_projection (hfree : ScalarFree τ S) (hτ : τ 1 = 1) (i : ι) :
    (headSpace τ S i).starProjection + (tailSpace τ S i).starProjection =
      (reducedSpace τ S).starProjection := by
  classical
  let Q := (headSpace τ S i).starProjection
  let T := (tailSpace τ S i).starProjection
  have horth := headSpace_orthogonal_tail hfree hτ i
  have horth' : tailSpace τ S i ≤ (headSpace τ S i)ᗮ := by
    intro x hx
    exact fun y hy => Submodule.inner_left_of_mem_orthogonal hx (horth hy)
  have hw : ∀ x ∈ reducedWords τ S, Q x + T x = x := by
    rintro x ⟨w, hw, rfl⟩
    by_cases ho : (w.map Prod.fst).head? = some i
    · have hm := headVector_mem hw ho
      rw [show Q (gnsVector τ (wordValue w)) = gnsVector τ (wordValue w) from
        Submodule.starProjection_eq_self_iff.mpr hm,
        show T (gnsVector τ (wordValue w)) = 0 from
        (Submodule.starProjection_apply_eq_zero_iff _).mpr (horth hm), add_zero]
    · have hm := tailVector_mem hw ho
      rw [show T (gnsVector τ (wordValue w)) = gnsVector τ (wordValue w) from
        Submodule.starProjection_eq_self_iff.mpr hm,
        show Q (gnsVector τ (wordValue w)) = 0 from
        (Submodule.starProjection_apply_eq_zero_iff _).mpr (horth' hm), zero_add]
  have hall : ∀ x ∈ reducedSpace τ S, Q x + T x = x := by
    intro x hx
    apply (closure_minimal (t := {z | Q z + T z = z}) ?_ ?_) hx
    · intro z hz
      change Q z + T z = z
      induction hz using Submodule.span_induction with
      | mem z hz => exact hw z hz
      | zero => simp
      | add x y hx hy ix iy => rw [map_add, map_add, add_add_add_comm, ix, iy]
      | smul c x hx ix => simp only [map_smul, ← smul_add, ix]
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (reducedSpace τ S).add_mem
      (headSpace_le_reducedSpace i (Submodule.starProjection_apply_mem _ _))
      (tailSpace_le_reducedSpace i (Submodule.starProjection_apply_mem _ _))
  · intro y hy
    change ⟪x - (Q x + T x), y⟫_ℂ = 0
    rw [inner_sub_left, inner_add_left]
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.inner_starProjection_left_eq_right, ← inner_add_right, hall y hy, sub_self]

def centerOf (τ : A →ₚ[ℂ] ℂ) (a : A) : A := a - τ a • 1

omit [StarOrderedRing A] in
theorem centerOf_mem {i : ι} {a : A} (ha : a ∈ S i) : centerOf τ a ∈ S i :=
  sub_mem ha ((S i).smul_mem (one_mem _) _)

omit [StarOrderedRing A] in
@[simp] theorem centerOf_trace (hτ : τ 1 = 1) (a : A) : τ (centerOf τ a) = 0 := by
  simp [centerOf, map_sub, map_smul, hτ]

theorem gnsVector_mul_split (a b : A) :
    gnsVector τ (a * b) = τ a • gnsVector τ b + gnsVector τ (centerOf τ a * b) := by
  rw [← map_smul, ← map_add]
  congr 1
  simp [centerOf, sub_mul]

omit [StarOrderedRing A] in
theorem Reduced.tail_headOutside {x : ι × A} {w : List (ι × A)}
    (h : Reduced (τ := τ) (S := S) (x :: w)) : HeadOutside x.1 w := by
  cases w with
  | nil => simp
  | cons y w =>
    rw [headOutside_cons]
    exact Ne.symm (List.isChain_cons_cons.mp h.1).1

theorem map_closedSpan_mem {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (L : E →L[ℂ] F) (s : Set E)
    (V : Submodule ℂ F) (hV : IsClosed (V : Set F))
    (hs : ∀ x ∈ s, L x ∈ V) {x : E} (hx : x ∈ (Submodule.span ℂ s).topologicalClosure) :
    L x ∈ V := by
  exact (Submodule.topologicalClosure_minimal _
    (show Submodule.span ℂ s ≤ V.comap L.toLinearMap from Submodule.span_le.mpr hs)
    (hV.preimage L.continuous)) hx

theorem mul_reducedVector_mem (hτ : τ 1 = 1) {i : ι} {a : A} (ha : a ∈ S i)
    {w : List (ι × A)} (hw : Reduced (τ := τ) (S := S) w) :
    τ.gnsStarAlgHom a (gnsVector τ (wordValue w)) ∈ reducedSpace τ S := by
  rw [gnsStarAlgHom_vector]
  by_cases ho : HeadOutside i w
  · rw [gnsVector_mul_split]
    apply (reducedSpace τ S).add_mem
      ((reducedSpace τ S).smul_mem _ (reducedVector_mem hw))
    exact reducedVector_mem (hw.cons_of_headOutside ho
      ⟨centerOf_mem ha, centerOf_trace hτ a⟩)
  · cases w with
    | nil => exact (ho (headOutside_nil i)).elim
    | cons x w =>
      have hi : x.1 = i := by simpa using ho
      rw [wordValue_cons, ← mul_assoc, gnsVector_mul_split]
      apply (reducedSpace τ S).add_mem
        ((reducedSpace τ S).smul_mem _ (reducedVector_mem hw.tail))
      have hx : x.2 ∈ S i := hi ▸ hw.head.1
      exact reducedVector_mem (hw.tail.cons_of_headOutside (hi ▸ hw.tail_headOutside)
        ⟨centerOf_mem (mul_mem ha hx), centerOf_trace hτ (a * x.2)⟩)

theorem mul_reducedSpace_mem (hτ : τ 1 = 1) {i : ι} {a : A} (ha : a ∈ S i)
    {x : τ.GNS} (hx : x ∈ reducedSpace τ S) :
    τ.gnsStarAlgHom a x ∈ reducedSpace τ S := by
  refine map_closedSpan_mem _ _ _ (Submodule.isClosed_topologicalClosure _) ?_ hx
  rintro y ⟨w, hw, rfl⟩
  exact mul_reducedVector_mem hτ ha hw

theorem create_mem_headSpace {i : ι} {a : A} (ha : a ∈ S i ∧ τ a = 0)
    {x : τ.GNS} (hx : x ∈ tailSpace τ S i) :
    τ.gnsStarAlgHom a x ∈ headSpace τ S i := by
  refine map_closedSpan_mem _ _ _ (Submodule.isClosed_topologicalClosure _) ?_ hx
  rintro y ⟨w, hw, ho, rfl⟩
  rw [gnsStarAlgHom_vector]
  exact headVector_mem (hw.cons_of_headOutside ho ha) rfl

theorem commute_projection_of_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (L : E →L[ℂ] E)
    (hL : ∀ x ∈ V, L x ∈ V) (hLs : ∀ x ∈ V, star L x ∈ V) :
    Commute L V.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  change L (V.starProjection x) = V.starProjection (L x)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hL _ (Submodule.starProjection_apply_mem _ _))
  intro y hy
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact Submodule.inner_left_of_mem_orthogonal (hLs y hy)
    (Submodule.sub_starProjection_mem_orthogonal x)

theorem copy_commutes_reducedProjection (hτ : τ 1 = 1) {i : ι} {a : A} (ha : a ∈ S i) :
    Commute (τ.gnsStarAlgHom a) (reducedSpace τ S).starProjection := by
  apply commute_projection_of_invariant
  · intro x hx; exact mul_reducedSpace_mem hτ ha hx
  · intro x hx
    rw [← map_star]
    exact mul_reducedSpace_mem hτ (star_mem ha) hx

def reductionAlgebra (τ : A →ₚ[ℂ] ℂ) (V : Submodule ℂ τ.GNS) [V.HasOrthogonalProjection] :
    StarSubalgebra ℂ A :=
  (StarSubalgebra.centralizer ℂ {V.starProjection}).comap τ.gnsStarAlgHom

theorem mem_reductionAlgebra (V : Submodule ℂ τ.GNS) [V.HasOrthogonalProjection] (a : A) :
    a ∈ reductionAlgebra τ V ↔ Commute (τ.gnsStarAlgHom a) V.starProjection := by
  simp only [reductionAlgebra, StarSubalgebra.mem_comap, StarSubalgebra.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq, (isSelfAdjoint_starProjection V).star_eq, and_self]
  exact eq_comm

instance reductionAlgebra_closed (V : Submodule ℂ τ.GNS) [V.HasOrthogonalProjection] :
    IsClosed (reductionAlgebra τ V : Set A) := by
  have he : (reductionAlgebra τ V : Set A) =
      {a | τ.gnsStarAlgHom a * V.starProjection = V.starProjection * τ.gnsStarAlgHom a} := by
    ext a; exact mem_reductionAlgebra V a
  rw [he]
  exact isClosed_eq (by fun_prop) (by fun_prop)

def compressedHom (V : Submodule ℂ τ.GNS) [V.HasOrthogonalProjection] :
    reductionAlgebra τ V →⋆ₙₐ[ℂ] (τ.GNS →L[ℂ] τ.GNS) where
  toFun a := τ.gnsStarAlgHom a * V.starProjection
  map_zero' := by simp
  map_add' a b := by simp [add_mul]
  map_smul' c a := by simp
  map_mul' a b := by
    change τ.gnsStarAlgHom ((a : A) * b) * V.starProjection = _
    rw [map_mul]
    have hb := (mem_reductionAlgebra V (b : A)).mp b.prop
    have hp := V.isIdempotentElem_starProjection.eq
    calc
      (τ.gnsStarAlgHom (a:A) * τ.gnsStarAlgHom (b:A)) * V.starProjection =
        τ.gnsStarAlgHom (a:A) * (τ.gnsStarAlgHom (b:A) *
          (V.starProjection * V.starProjection)) := by rw [hp, mul_assoc]
      _ = (τ.gnsStarAlgHom (a:A) * V.starProjection) *
          (τ.gnsStarAlgHom (b:A) * V.starProjection) := by
        calc
          _ = τ.gnsStarAlgHom (a:A) * ((τ.gnsStarAlgHom (b:A) * V.starProjection) *
            V.starProjection) := by simp only [mul_assoc]
          _ = τ.gnsStarAlgHom (a:A) * ((V.starProjection * τ.gnsStarAlgHom (b:A)) *
            V.starProjection) := congrArg (fun t => τ.gnsStarAlgHom (a:A) * (t * V.starProjection)) hb.eq
          _ = _ := by simp only [mul_assoc]
  map_star' a := by
    change τ.gnsStarAlgHom (star (a : A)) * V.starProjection = _
    rw [star_mul, (isSelfAdjoint_starProjection V).star_eq, ← map_star]
    exact (mem_reductionAlgebra V (star (a : A))).mp (star_mem a.prop)

theorem compressedHom_injective (V : Submodule ℂ τ.GNS) [V.HasOrthogonalProjection]
    (hV : gnsVector τ 1 ∈ V) (hf : ∀ x : A, τ (star x * x) = 0 → x = 0) :
    Function.Injective (compressedHom (τ := τ) V) := by
  intro a b hab
  apply Subtype.ext
  apply gnsVector_injective hf
  have h := congrArg (fun L : τ.GNS →L[ℂ] τ.GNS => L (gnsVector τ 1)) hab
  change τ.gnsStarAlgHom (a:A) (V.starProjection (gnsVector τ 1)) =
    τ.gnsStarAlgHom (b:A) (V.starProjection (gnsVector τ 1)) at h
  simpa only [Submodule.starProjection_eq_self_iff.mpr hV, gnsStarAlgHom_vector, mul_one] using h

theorem norm_compressed (V : Submodule ℂ τ.GNS) [V.HasOrthogonalProjection]
    (hV : gnsVector τ 1 ∈ V) (hf : ∀ x : A, τ (star x * x) = 0 → x = 0)
    (a : A) (ha : Commute (τ.gnsStarAlgHom a) V.starProjection) :
    ‖τ.gnsStarAlgHom a * V.starProjection‖ = ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_map (compressedHom (τ := τ) V)
    (compressedHom_injective V hV hf) ⟨a, (mem_reductionAlgebra V a).mpr ha⟩

def creationOp (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) (i : ι) (a : A) :=
  τ.gnsStarAlgHom a * (tailSpace τ S i).starProjection

def preservationOp (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) (i : ι) (a : A) :=
  (headSpace τ S i).starProjection * τ.gnsStarAlgHom a * (headSpace τ S i).starProjection

def letterOp (τ : A →ₚ[ℂ] ℂ) (S : ι → StarSubalgebra ℂ A) (a : A) :=
  τ.gnsStarAlgHom a * (reducedSpace τ S).starProjection

theorem head_mul_creation {i : ι} {a : A} (ha : a ∈ S i ∧ τ a = 0) :
    (headSpace τ S i).starProjection * creationOp τ S i a = creationOp τ S i a := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact create_mem_headSpace ha (Submodule.starProjection_apply_mem _ _)

theorem annihilation_mul_head {i : ι} {a : A} (ha : a ∈ S i ∧ τ a = 0) :
    star (creationOp τ S i a) * (headSpace τ S i).starProjection =
      star (creationOp τ S i a) := by
  simpa only [star_mul, (isSelfAdjoint_starProjection _).star_eq] using
    congrArg star (head_mul_creation ha)

theorem head_mul_preservation (i : ι) (a : A) :
    (headSpace τ S i).starProjection * preservationOp τ S i a = preservationOp τ S i a := by
  simp only [preservationOp, ← mul_assoc, (headSpace τ S i).isIdempotentElem_starProjection.eq]

theorem preservation_mul_head (i : ι) (a : A) :
    preservationOp τ S i a * (headSpace τ S i).starProjection = preservationOp τ S i a := by
  simp only [preservationOp, mul_assoc, (headSpace τ S i).isIdempotentElem_starProjection.eq]

theorem head_mul_head_zero (hfree : ScalarFree τ S) (hτ : τ 1 = 1) {i j : ι} (hij : i ≠ j) :
    (headSpace τ S i).starProjection * (headSpace τ S j).starProjection = 0 := by
  ext x
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  exact Submodule.orthogonal_le (headSpace_le_tailSpace hij)
    (headSpace_orthogonal_tail hfree hτ j (Submodule.starProjection_apply_mem _ _))

theorem letterOp_decomposition (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    {i : ι} {a : A} (ha : a ∈ S i ∧ τ a = 0) (hsa : star a = a) :
    letterOp τ S a = creationOp τ S i a + star (creationOp τ S i a) +
      preservationOp τ S i a := by
  let Q := (headSpace τ S i).starProjection
  let T := (tailSpace τ S i).starProjection
  let V := (reducedSpace τ S).starProjection
  let L := τ.gnsStarAlgHom a
  have hvq : V * Q = Q := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr
      (headSpace_le_reducedSpace i (Submodule.starProjection_apply_mem _ _))
  have hvl : V * L = L * V := (copy_commutes_reducedProjection hτ ha.1).symm.eq
  have hsum : Q + T = V := head_add_tail_projection hfree hτ i
  have hstar : star (creationOp τ S i a) = T * L := by
    simp only [creationOp, star_mul, ← map_star, hsa, (isSelfAdjoint_starProjection _).star_eq]
    rfl
  have hsupport : T * L * Q = T * L := by
    rw [← hstar, annihilation_mul_head ha]
  change L * V = _
  calc
    L * V = L * Q + L * T := by rw [← hsum, mul_add]
    _ = (Q * L * Q + T * L * Q) + L * T := by
      congr 1
      rw [← add_mul, ← add_mul, hsum, hvl, mul_assoc, hvq]
    _ = creationOp τ S i a + star (creationOp τ S i a) + preservationOp τ S i a := by
      rw [hsupport, ← hstar]
      dsimp only [creationOp, preservationOp, Q, T, L]
      abel

theorem annihilation_mul_creation_zero (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ S i ∧ τ a = 0) (hb : b ∈ S j ∧ τ b = 0) :
    star (creationOp τ S i a) * creationOp τ S j b = 0 := by
  calc
    _ = (star (creationOp τ S i a) * (headSpace τ S i).starProjection) *
      ((headSpace τ S j).starProjection * creationOp τ S j b) := by
        rw [annihilation_mul_head ha, head_mul_creation hb]
    _ = 0 := by
      simp only [mul_assoc, ← mul_assoc (headSpace τ S i).starProjection,
        head_mul_head_zero hfree hτ hij, zero_mul, mul_zero]

theorem preservation_mul_creation_zero (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    {i j : ι} (hij : i ≠ j) {a b : A} (hb : b ∈ S j ∧ τ b = 0) :
    preservationOp τ S i a * creationOp τ S j b = 0 := by
  calc
    _ = (preservationOp τ S i a * (headSpace τ S i).starProjection) *
      ((headSpace τ S j).starProjection * creationOp τ S j b) := by
        rw [preservation_mul_head, head_mul_creation hb]
    _ = 0 := by
      simp only [mul_assoc, ← mul_assoc (headSpace τ S i).starProjection,
        head_mul_head_zero hfree hτ hij, zero_mul, mul_zero]

theorem annihilation_mul_preservation_zero (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    {i j : ι} (hij : i ≠ j) {a b : A} (ha : a ∈ S i ∧ τ a = 0) :
    star (creationOp τ S i a) * preservationOp τ S j b = 0 := by
  calc
    _ = (star (creationOp τ S i a) * (headSpace τ S i).starProjection) *
      ((headSpace τ S j).starProjection * preservationOp τ S j b) := by
        rw [annihilation_mul_head ha, head_mul_preservation]
    _ = 0 := by
      simp only [mul_assoc, ← mul_assoc (headSpace τ S i).starProjection,
        head_mul_head_zero hfree hτ hij, zero_mul, mul_zero]

theorem preservation_mul_preservation_zero (hfree : ScalarFree τ S) (hτ : τ 1 = 1)
    {i j : ι} (hij : i ≠ j) (a b : A) :
    preservationOp τ S i a * preservationOp τ S j b = 0 := by
  calc
    _ = (preservationOp τ S i a * (headSpace τ S i).starProjection) *
      ((headSpace τ S j).starProjection * preservationOp τ S j b) := by
        rw [preservation_mul_head, head_mul_preservation]
    _ = 0 := by
      simp only [mul_assoc, ← mul_assoc (headSpace τ S i).starProjection,
        head_mul_head_zero hfree hτ hij, zero_mul, mul_zero]

namespace FreePartitions

variable {r d : ℕ} (P : FreePartitions τ r d)

def centered (j : Fin r) (a : Fin d) : A := P.e j a - (d : ℂ)⁻¹ • 1

omit [StarOrderedRing A] in
@[simp] theorem centered_star (j : Fin r) (a : Fin d) :
    star (P.centered j a) = P.centered j a := by
  simp only [centered, star_sub, P.selfadjoint, star_smul, star_inv₀, star_natCast,
    star_one]

omit [StarOrderedRing A] in
theorem centered_mem (j : Fin r) (a : Fin d) : P.centered j a ∈ P.S j :=
  sub_mem (P.mem j a) ((P.S j).smul_mem (one_mem _) _)

omit [StarOrderedRing A] in
@[simp] theorem centered_trace (hτ : τ 1 = 1) (j : Fin r) (a : Fin d) :
    τ (P.centered j a) = 0 := by
  simp [centered, map_sub, map_smul, P.trace, hτ]

omit [StarOrderedRing A] in
theorem centered_gram (hτ : τ 1 = 1) (j : Fin r) (a b : Fin d) :
    τ (star (P.centered j a) * P.centered j b) =
      (if a = b then (d : ℂ)⁻¹ else 0) - (d : ℂ)⁻¹ * (d : ℂ)⁻¹ := by
  rw [P.centered_star]
  simp only [centered, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    mul_one, one_mul, map_sub, map_smul, P.trace, P.mul, hτ, smul_eq_mul]
  split_ifs <;> simp [P.trace]

theorem inner_create_row (hτ : τ 1 = 1) (j : Fin r) (ξ : Fin d → τ.GNS)
    (hξ : ∀ a, ξ a ∈ tailSpace τ P.S j) :
    ⟪∑ a, τ.gnsStarAlgHom (P.centered j a) (ξ a),
      ∑ a, τ.gnsStarAlgHom (P.centered j a) (ξ a)⟫_ℂ =
      (d : ℂ)⁻¹ * (∑ a, ⟪ξ a, ξ a⟫_ℂ) -
        ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) * ⟪∑ a, ξ a, ∑ a, ξ a⟫_ℂ := by
  classical
  simp only [sum_inner, inner_sum]
  have heq : ∀ a b : Fin d,
      ⟪τ.gnsStarAlgHom (P.centered j a) (ξ a),
        τ.gnsStarAlgHom (P.centered j b) (ξ b)⟫_ℂ =
      (if a = b then (d : ℂ)⁻¹ * ⟪ξ a, ξ b⟫_ℂ else 0) -
        ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) * ⟪ξ a, ξ b⟫_ℂ := by
    intro a b
    rw [inner_create P.free hτ ⟨P.centered_mem j a, P.centered_trace hτ j a⟩
      ⟨P.centered_mem j b, P.centered_trace hτ j b⟩ (hξ a) (hξ b),
      P.centered_gram hτ, sub_mul]
    split_ifs <;> simp
  simp only [heq, Finset.sum_sub_distrib, Finset.mul_sum]
  simp

theorem norm_create_row_sq (hτ : τ 1 = 1) (j : Fin r) (ξ : Fin d → τ.GNS)
    (hξ : ∀ a, ξ a ∈ tailSpace τ P.S j) :
    ‖∑ a, τ.gnsStarAlgHom (P.centered j a) (ξ a)‖ ^ 2 =
      (d : ℝ)⁻¹ * (∑ a, ‖ξ a‖ ^ 2) -
        ((d : ℝ)⁻¹ * (d : ℝ)⁻¹) * ‖∑ a, ξ a‖ ^ 2 := by
  have h := P.inner_create_row hτ j ξ hξ
  simp only [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_sum, Complex.ofReal_pow] using h

end FreePartitions

end

end KKFreeWords
end

end OAI
