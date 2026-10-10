import OAI.Analysis.LiebThirring.FiniteParity

namespace OAI

universe u68 u69 u70 u71 u72 u73 u74 u75 u76 u77 u78 u79 u80 u81 u82 u83 u84 u85 u86 u87 u88 u89 u90 u91 u92 u93 u94 u191 u192

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset


section


/-! Generic vertex positions for the piecewise-linear continuation argument. -/

open Set Finset Filter
namespace SharpLiebThirring.PLParity

variable {V : Type u68} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
lemma dense_compl_proper_submodule (S : Submodule ℝ V) (hS : S ≠ ⊤) :
    Dense (S : Set V)ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  by_contra h
  exact hS (S.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.mpr h))

omit [FiniteDimensional ℝ V] in
lemma dense_linearIndependent_fin (n : ℕ) (hn : n ≤ Module.finrank ℝ V) :
    Dense {v : Fin n → V | LinearIndependent ℝ v} := by
  induction n with
  | zero =>
      have : {v : Fin 0 → V | LinearIndependent ℝ v} = Set.univ := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact linearIndependent_empty_type
      rw [this]
      exact dense_univ
  | succ n ih =>
      rw [Metric.dense_iff]
      intro v ε hε
      obtain ⟨w, hw, hwε⟩ := (ih (by omega)).exists_dist_lt (Fin.tail v) hε
      let S : Submodule ℝ V := Submodule.span ℝ (Set.range w)
      have hS : S ≠ ⊤ := by
        intro he
        have hd := finrank_span_eq_card hw
        change Module.finrank ℝ S = Fintype.card (Fin n) at hd
        rw [he, finrank_top, Fintype.card_fin] at hd
        omega
      obtain ⟨x, hx, hxε⟩ := (dense_compl_proper_submodule S hS).exists_dist_lt (v 0) hε
      refine ⟨Fin.cons x w, ?_, linearIndependent_finCons.mpr ⟨hw, hx⟩⟩
      apply (dist_pi_lt_iff hε).mpr
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa [dist_comm] using hxε
      · simpa [Fin.tail, dist_comm] using (dist_pi_lt_iff hε).mp hwε j

omit [FiniteDimensional ℝ V] in
lemma dense_linearIndependent {ι : Type u69} [Fintype ι]
    (hn : Fintype.card ι ≤ Module.finrank ℝ V) :
    Dense {v : ι → V | LinearIndependent ℝ v} := by
  classical
  rw [Metric.dense_iff]
  intro v ε hε
  let e := Fintype.equivFin ι
  obtain ⟨w, hw, hwε⟩ := (dense_linearIndependent_fin (Fintype.card ι) hn).exists_dist_lt
    (v ∘ e.symm) hε
  refine ⟨w ∘ e, ?_, hw.comp e e.injective⟩
  apply (dist_pi_lt_iff hε).mpr
  intro i
  simpa [Function.comp_def, dist_comm] using (dist_pi_lt_iff hε).mp hwε (e i)

/-- Put a new extension vector before the previous extension vectors. -/
def sumFinSuccEmbedding (ι : Type u70) (n : ℕ) :
    ι ⊕ Fin (n + 1) ↪ Option (ι ⊕ Fin n) where
  toFun := Sum.elim (fun i ↦ some (Sum.inl i))
    (Fin.cases none (fun j ↦ some (Sum.inr j)))
  inj' := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp
    · refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp
    · refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp
    · refine Fin.cases ?_ (fun i ↦ ?_) i <;>
        refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp

omit [FiniteDimensional ℝ V] in
lemma dense_linearIndependent_extension {ι : Type u71} [Fintype ι]
    (v : ι → V) (hv : LinearIndependent ℝ v) (n : ℕ)
    (hn : Fintype.card ι + n ≤ Module.finrank ℝ V) :
    Dense {w : Fin n → V | LinearIndependent ℝ (Sum.elim v w)} := by
  classical
  induction n with
  | zero =>
      have he : {w : Fin 0 → V | LinearIndependent ℝ (Sum.elim v w)} = Set.univ := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        rw [linearIndependent_sum]
        refine ⟨hv, linearIndependent_empty_type, ?_⟩
        simp
      rw [he]
      exact dense_univ
  | succ n ih =>
      rw [Metric.dense_iff]
      intro w ε hε
      obtain ⟨z, hz, hzε⟩ := (ih (by omega)).exists_dist_lt (Fin.tail w) hε
      let S : Submodule ℝ V := Submodule.span ℝ (Set.range (Sum.elim v z))
      have hS : S ≠ ⊤ := by
        intro he
        have hd := finrank_span_eq_card hz
        change Module.finrank ℝ S = Fintype.card (ι ⊕ Fin n) at hd
        rw [he, finrank_top, Fintype.card_sum, Fintype.card_fin] at hd
        omega
      obtain ⟨x, hx, hxε⟩ := (dense_compl_proper_submodule S hS).exists_dist_lt (w 0) hε
      refine ⟨Fin.cons x z, ?_, ?_⟩
      · apply (dist_pi_lt_iff hε).mpr
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa [dist_comm] using hxε
        · simpa [Fin.tail, dist_comm] using (dist_pi_lt_iff hε).mp hzε j
      · have hl := (hz.option hx).comp (sumFinSuccEmbedding ι n)
          (sumFinSuccEmbedding ι n).injective
        change LinearIndependent ℝ (Sum.elim v (Fin.cons x z))
        have heq : Sum.elim v (Fin.cons x z) =
            (fun o ↦ o.casesOn' x (Sum.elim v z)) ∘ (sumFinSuccEmbedding ι n) := by
          ext i
          rcases i with i | i
          · rfl
          · exact Fin.cases rfl (fun j ↦ rfl) i
        rw [heq]
        exact hl

lemma dense_augmented_linearIndependent {ι : Type u72} [Fintype ι]
    (hn : Fintype.card ι ≤ Module.finrank ℝ V + 1) :
    Dense {v : ι → V | LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))} := by
  classical
  rw [Metric.dense_iff]
  intro v ε hε
  let a : ι → ℝ × V := fun i ↦ (1, v i)
  let normal : (ι → ℝ × V) → (ι → V) := fun u i ↦ (u i).1⁻¹ • (u i).2
  have hnorm : ContinuousAt normal a := by
    apply continuousAt_pi.mpr
    intro i
    exact (((continuous_apply i).fst.continuousAt).inv₀ (by norm_num [a])).smul
      (continuous_apply i).snd.continuousAt
  have hnval : normal a = v := by ext i; simp [normal, a]
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousAt_iff.mp hnorm ε hε
  obtain ⟨u, hu, huδ⟩ := (dense_linearIndependent (V := ℝ × V)
    (ι := ι) (by simpa [Module.finrank_prod, Nat.add_comm] using hn)).exists_dist_lt a
    (lt_min hδ (by norm_num : (0 : ℝ) < 1))
  rw [dist_comm] at huδ
  have hfst (i : ι) : (u i).1 ≠ 0 := by
    intro he
    have hdi : dist (u i) (a i) < 1 :=
      lt_of_lt_of_le ((dist_pi_lt_iff (lt_min hδ (by norm_num))).mp huδ i) (min_le_right _ _)
    rw [Prod.dist_eq] at hdi
    have hdf := (max_lt_iff.mp hdi).1
    simp [he, a] at hdf
  refine ⟨normal u, ?_, ?_⟩
  · have hd := hcδ (lt_of_lt_of_le huδ (min_le_left _ _))
    simpa [hnval, dist_comm] using hd
  · change LinearIndependent ℝ (fun i ↦ ((1 : ℝ), normal u i))
    have hul := hu.units_smul (fun i ↦ (Units.mk0 (u i).1 (hfst i))⁻¹)
    have heq : (fun i ↦ ((1 : ℝ), normal u i)) =
        (fun i ↦ (Units.mk0 (u i).1 (hfst i))⁻¹) • u := by
      ext i <;> simp [normal, Units.smul_def, hfst i]
    rw [heq]
    exact hul

lemma dense_augmentedIndependent_extension_fin {ι : Type u73} [Fintype ι]
    (v : ι → V) (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) (n : ℕ)
    (hn : Fintype.card ι + n ≤ Module.finrank ℝ V + 1) :
    Dense {w : Fin n → V | LinearIndependent ℝ
      (fun i ↦ ((1 : ℝ), Sum.elim v w i))} := by
  classical
  rw [Metric.dense_iff]
  intro w ε hε
  let a : Fin n → ℝ × V := fun i ↦ (1, w i)
  let normal : (Fin n → ℝ × V) → (Fin n → V) := fun u i ↦ (u i).1⁻¹ • (u i).2
  have hnorm : ContinuousAt normal a := by
    apply continuousAt_pi.mpr
    intro i
    exact (((continuous_apply i).fst.continuousAt).inv₀ (by norm_num [a])).smul
      (continuous_apply i).snd.continuousAt
  have hnval : normal a = w := by ext i; simp [normal, a]
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousAt_iff.mp hnorm ε hε
  obtain ⟨u, hu, huδ⟩ := (dense_linearIndependent_extension
    (V := ℝ × V) (fun i ↦ ((1 : ℝ), v i)) hv n
    (by simpa [Module.finrank_prod, Nat.add_comm] using hn)).exists_dist_lt a
    (lt_min hδ (by norm_num : (0 : ℝ) < 1))
  rw [dist_comm] at huδ
  have hfst (i : Fin n) : (u i).1 ≠ 0 := by
    intro he
    have hdi : dist (u i) (a i) < 1 :=
      lt_of_lt_of_le ((dist_pi_lt_iff (lt_min hδ (by norm_num))).mp huδ i) (min_le_right _ _)
    rw [Prod.dist_eq] at hdi
    have hdf := (max_lt_iff.mp hdi).1
    simp [he, a] at hdf
  refine ⟨normal u, ?_, ?_⟩
  · have hd := hcδ (lt_of_lt_of_le huδ (min_le_left _ _))
    simpa [hnval, dist_comm] using hd
  · let c : ι ⊕ Fin n → ℝˣ := Sum.elim (fun _ ↦ 1)
      (fun i ↦ (Units.mk0 (u i).1 (hfst i))⁻¹)
    have hul := hu.units_smul c
    change LinearIndependent ℝ (fun i ↦ ((1 : ℝ), Sum.elim v (normal u) i))
    have heq : (fun i ↦ ((1 : ℝ), Sum.elim v (normal u) i)) =
        c • Sum.elim (fun i ↦ ((1 : ℝ), v i)) u := by
      funext i
      rcases i with i | i <;> ext <;> simp [c, normal, Units.smul_def, hfst]
    rw [heq]
    exact hul

omit [FiniteDimensional ℝ V] in
lemma dense_linearIndependent_extension_fintype {ι : Type u74} {κ : Type u75} [Fintype ι] [Fintype κ]
    (v : ι → V) (hv : LinearIndependent ℝ v)
    (hn : Fintype.card ι + Fintype.card κ ≤ Module.finrank ℝ V) :
    Dense {w : κ → V | LinearIndependent ℝ (Sum.elim v w)} := by
  classical
  rw [Metric.dense_iff]
  intro w ε hε
  let e := Fintype.equivFin κ
  obtain ⟨z, hz, hzε⟩ := (dense_linearIndependent_extension v hv (Fintype.card κ) hn).exists_dist_lt (w ∘ e.symm) hε
  refine ⟨z ∘ e, ?_, ?_⟩
  · apply (dist_pi_lt_iff hε).mpr
    intro i
    simpa [Function.comp_def, dist_comm] using (dist_pi_lt_iff hε).mp hzε (e i)
  · have heq : Sum.elim v (z ∘ e) =
        (Sum.elim v z) ∘ (Equiv.sumCongr (Equiv.refl ι) e) := by
      funext i
      cases i <;> rfl
    change LinearIndependent ℝ (Sum.elim v (z ∘ e))
    rw [heq]
    exact hz.comp _ (Equiv.sumCongr (Equiv.refl ι) e).injective

lemma dense_augmentedIndependent_extension {ι : Type u76} {κ : Type u77} [Fintype ι] [Fintype κ]
    (v : ι → V) (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i)))
    (hn : Fintype.card ι + Fintype.card κ ≤ Module.finrank ℝ V + 1) :
    Dense {w : κ → V | LinearIndependent ℝ (fun i ↦ ((1 : ℝ), Sum.elim v w i))} := by
  classical
  rw [Metric.dense_iff]
  intro w ε hε
  let e := Fintype.equivFin κ
  obtain ⟨z, hz, hzε⟩ := (dense_augmentedIndependent_extension_fin v hv (Fintype.card κ) hn).exists_dist_lt (w ∘ e.symm) hε
  refine ⟨z ∘ e, ?_, ?_⟩
  · apply (dist_pi_lt_iff hε).mpr
    intro i
    simpa [Function.comp_def, dist_comm] using (dist_pi_lt_iff hε).mp hzε (e i)
  · have heq : (fun i ↦ ((1 : ℝ), Sum.elim v (z ∘ e) i)) =
        (fun i ↦ ((1 : ℝ), Sum.elim v z i)) ∘ (Equiv.sumCongr (Equiv.refl ι) e) := by
      funext i
      cases i <;> rfl
    change LinearIndependent ℝ (fun i ↦ ((1 : ℝ), Sum.elim v (z ∘ e) i))
    rw [heq]
    exact hz.comp _ (Equiv.sumCongr (Equiv.refl ι) e).injective

omit [FiniteDimensional ℝ V] in
lemma affineIndependent_of_augmented {ι : Type u78} (v : ι → V)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) : AffineIndependent ℝ v := by
  rw [affineIndependent_iff]
  intro s w hs hsum i hi
  apply (linearIndependent_iff'.mp hv) s w _ i hi
  apply Prod.ext
  · simpa [Prod.fst_sum] using hs
  · simpa [Prod.snd_sum] using hsum

omit [FiniteDimensional ℝ V] in
lemma independent_shift_of_augmented_extra {ι : Type u79} (v : ι → V) (a : V)
    (hv : LinearIndependent ℝ
      (fun i : ι ⊕ Unit ↦ ((1 : ℝ), Sum.elim v (fun _ ↦ a) i))) :
    LinearIndependent ℝ (fun i ↦ v i - a) := by
  have hh := (affineIndependent_iff_linearIndependent_vsub ℝ
    (Sum.elim v (fun _ : Unit ↦ a)) (Sum.inr ())).mp (affineIndependent_of_augmented _ hv)
  let e : ι → {i : ι ⊕ Unit // i ≠ Sum.inr ()} := fun i ↦ ⟨Sum.inl i, by simp⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Sum.inl.inj (congrArg Subtype.val hij)
  exact hh.comp e he

/-- A generic root avoids the affine hull of every prescribed independent
proper face. This permits an initial zero inside exactly one maximal flag. -/
lemma dense_independent_shift {ι : Type u80} [Fintype ι] (v : ι → V)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i)))
    (hn : Fintype.card ι ≤ Module.finrank ℝ V) :
    Dense {a : V | LinearIndependent ℝ (fun i ↦ v i - a)} := by
  classical
  rw [Metric.dense_iff]
  intro a ε hε
  have hc : Fintype.card ι + Fintype.card Unit ≤ Module.finrank ℝ V + 1 := by
    simpa using Nat.add_le_add_right hn 1
  obtain ⟨w, hw, hwε⟩ := (dense_augmentedIndependent_extension v hv hc).exists_dist_lt
    (fun _ : Unit ↦ a) hε
  refine ⟨w (), ?_, independent_shift_of_augmented_extra v (w ()) ?_⟩
  · exact (dist_comm _ _).le.trans_lt ((dist_pi_lt_iff hε).mp hwε ())
  · have he : w = (fun _ : Unit ↦ w ()) := by funext i; cases i; rfl
    rw [he] at hw
    exact hw

omit [FiniteDimensional ℝ V] in
lemma isOpen_independent_shift {ι : Type u81} [Fintype ι] (v : ι → V) :
    IsOpen {a : V | LinearIndependent ℝ (fun i ↦ v i - a)} := by
  apply isOpen_setOfPred_linearIndependent.preimage
  exact continuous_pi (fun _ ↦ continuous_const.sub continuous_id)

/-- Positive barycentric coordinates remain positive on a neighborhood when
an augmented vertex family is a basis. -/
lemma positive_barycentric_neighborhood {ι : Type u82} [Fintype ι]
    (v : ι → V) (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i)))
    (hn : Fintype.card ι = Module.finrank ℝ V + 1)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hs : ∑ i, w i = 1) :
    ∃ U : Set V, IsOpen U ∧ (∑ i, w i • v i) ∈ U ∧
      ∀ x ∈ U, ∃ z : ι → ℝ, (∀ i, 0 < z i) ∧ ∑ i, z i = 1 ∧ ∑ i, z i • v i = x := by
  classical
  let B : Module.Basis ι ℝ (ℝ × V) := basisOfLinearIndependentOfCardEqFinrank'
    (fun i ↦ ((1 : ℝ), v i)) hv (by simpa [Module.finrank_prod, Nat.add_comm] using hn)
  have hB (i : ι) : B i = ((1 : ℝ), v i) := by
    simp [B]
  let z : V → ι → ℝ := fun x ↦ B.equivFun (1, x)
  have hz : Continuous z := B.equivFun.toContinuousLinearEquiv.continuous.comp
    (continuous_const.prodMk continuous_id)
  have hrep (x : V) : ∑ i, z x i • ((1 : ℝ), v i) = (1, x) := by
    simpa only [z, Module.Basis.equivFun_apply, hB] using B.sum_repr (1, x)
  let x₀ : V := ∑ i, w i • v i
  have hzw : z x₀ = w := by
    apply B.equivFun.symm.injective
    change B.equivFun.symm (B.equivFun (1, x₀)) = B.equivFun.symm w
    rw [B.equivFun.symm_apply_apply, Module.Basis.equivFun_symm_apply]
    apply Prod.ext
    · simp only [hB, Prod.fst_sum, Prod.smul_fst, smul_eq_mul, mul_one, hs]
    · simp only [hB, Prod.snd_sum, Prod.smul_snd]
      rfl
  refine ⟨{x | ∀ i, 0 < z x i}, ?_, ?_, ?_⟩
  · have ho : IsOpen (⋂ i, {x | (0 : ℝ) < z x i}) := isOpen_iInter_of_finite
      (fun i ↦ isOpen_lt continuous_const ((continuous_apply i).comp hz))
    simpa only [Set.ofPred_forall] using ho
  · change ∀ i, 0 < z x₀ i
    rwa [hzw]
  · intro x hx
    refine ⟨z x, hx, ?_, ?_⟩
    · simpa only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul, mul_one] using congrArg Prod.fst (hrep x)
    · simpa only [Prod.snd_sum, Prod.smul_snd] using congrArg Prod.snd (hrep x)

section VertexEvaluation
variable {Q : Type u83} {ι : Type u84} [Fintype Q] [Fintype ι]

/-- On distinct vertex orbits, equivariant vertex values may be varied independently. -/
def vertexEvaluation (e : ι → Q) (A : ι → V ≃ₗ[ℝ] V) :
    (Q → V) →ₗ[ℝ] (ι → V) where
  toFun w i := A i (w (e i))
  map_add' w z := by ext i; simp
  map_smul' c w := by ext i; simp

omit [FiniteDimensional ℝ V] [Fintype Q] [Fintype ι] in
lemma vertexEvaluation_surjective (e : ι → Q) (he : Function.Injective e)
    (A : ι → V ≃ₗ[ℝ] V) : Function.Surjective (vertexEvaluation e A) := by
  classical
  intro v
  refine ⟨Function.extend e (fun i ↦ (A i).symm (v i)) 0, ?_⟩
  ext i
  simp only [vertexEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    he.extend_apply, LinearEquiv.apply_symm_apply]

lemma vertexEvaluation_isOpenMap (e : ι → Q) (he : Function.Injective e)
    (A : ι → V ≃ₗ[ℝ] V) : IsOpenMap (vertexEvaluation e A) :=
  (vertexEvaluation e A).toContinuousLinearMap.isOpenMap
    (vertexEvaluation_surjective e he A)

omit [Fintype ι] in
lemma vertexEvaluation_continuous (e : ι → Q) (A : ι → V ≃ₗ[ℝ] V) :
    Continuous (vertexEvaluation e A) :=
  (vertexEvaluation e A).toContinuousLinearMap.continuous

lemma dense_vertex_linearlyIndependent (e : ι → Q) (he : Function.Injective e)
    (A : ι → V ≃ₗ[ℝ] V) (hn : Fintype.card ι ≤ Module.finrank ℝ V) :
    Dense {w : Q → V | LinearIndependent ℝ (vertexEvaluation e A w)} :=
  (dense_linearIndependent hn).preimage (vertexEvaluation_isOpenMap e he A)

lemma dense_vertex_augmentedIndependent (e : ι → Q) (he : Function.Injective e)
    (A : ι → V ≃ₗ[ℝ] V) (hn : Fintype.card ι ≤ Module.finrank ℝ V + 1) :
    Dense {w : Q → V | LinearIndependent ℝ (fun i ↦ ((1 : ℝ), vertexEvaluation e A w i))} :=
  (dense_augmented_linearIndependent hn).preimage (vertexEvaluation_isOpenMap e he A)

lemma isOpen_vertex_linearlyIndependent (e : ι → Q) (A : ι → V ≃ₗ[ℝ] V) :
    IsOpen {w : Q → V | LinearIndependent ℝ (vertexEvaluation e A w)} :=
  isOpen_setOfPred_linearIndependent.preimage (vertexEvaluation_continuous e A)

lemma isOpen_vertex_augmentedIndependent (e : ι → Q) (A : ι → V ≃ₗ[ℝ] V) :
    IsOpen {w : Q → V | LinearIndependent ℝ (fun i ↦ ((1 : ℝ), vertexEvaluation e A w i))} := by
  apply isOpen_setOfPred_linearIndependent.preimage
  exact continuous_pi (fun i ↦ continuous_const.prodMk
    ((continuous_apply i).comp (vertexEvaluation_continuous e A)))

/-- Genericity may be imposed while retaining an independent prescribed part.
This is used for the initial boundary of the continuation cylinder. -/
lemma dense_vertex_independent_extension {κ : Type u85} [Fintype κ]
    (v : κ → V) (hv : LinearIndependent ℝ v)
    (e : ι → Q) (he : Function.Injective e) (A : ι → V ≃ₗ[ℝ] V)
    (hn : Fintype.card κ + Fintype.card ι ≤ Module.finrank ℝ V) :
    Dense {w : Q → V | LinearIndependent ℝ (Sum.elim v (vertexEvaluation e A w))} :=
  (dense_linearIndependent_extension_fintype v hv hn).preimage
    (vertexEvaluation_isOpenMap e he A)

lemma dense_vertex_augmented_extension {κ : Type u86} [Fintype κ]
    (v : κ → V) (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i)))
    (e : ι → Q) (he : Function.Injective e) (A : ι → V ≃ₗ[ℝ] V)
    (hn : Fintype.card κ + Fintype.card ι ≤ Module.finrank ℝ V + 1) :
    Dense {w : Q → V | LinearIndependent ℝ
      (fun i ↦ ((1 : ℝ), Sum.elim v (vertexEvaluation e A w) i))} :=
  (dense_augmentedIndependent_extension v hv hn).preimage
    (vertexEvaluation_isOpenMap e he A)

lemma isOpen_vertex_independent_extension {κ : Type u87} [Fintype κ]
    (v : κ → V) (e : ι → Q) (A : ι → V ≃ₗ[ℝ] V) :
    IsOpen {w : Q → V | LinearIndependent ℝ (Sum.elim v (vertexEvaluation e A w))} := by
  apply isOpen_setOfPred_linearIndependent.preimage
  apply continuous_pi
  rintro (i | i)
  · exact continuous_const
  · exact (continuous_apply i).comp (vertexEvaluation_continuous e A)

lemma isOpen_vertex_augmented_extension {κ : Type u88} [Fintype κ]
    (v : κ → V) (e : ι → Q) (A : ι → V ≃ₗ[ℝ] V) :
    IsOpen {w : Q → V | LinearIndependent ℝ
      (fun i ↦ ((1 : ℝ), Sum.elim v (vertexEvaluation e A w) i))} := by
  apply isOpen_setOfPred_linearIndependent.preimage
  apply continuous_pi
  rintro (i | i)
  · change Continuous (fun _ : Q → V ↦ ((1 : ℝ), v i))
    exact continuous_const
  · exact continuous_const.prodMk
      ((continuous_apply i).comp (vertexEvaluation_continuous e A))

attribute [local instance] Classical.propDecidable

/-- Extend vertex values on the free orbits while retaining the prescribed orbits. -/
def mixedVertexEvaluation (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (A : ι → V ≃ₗ[ℝ] V) (a : {q // ¬ P q} → V) (i : ι) : V :=
  A i (if h : P (e i) then b (e i) else a ⟨e i, h⟩)

omit [Fintype Q] [Fintype ι] in
lemma mixedVertexEvaluation_continuous (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (A : ι → V ≃ₗ[ℝ] V) : Continuous (mixedVertexEvaluation P b e A) := by
  apply continuous_pi
  intro i
  by_cases h : P (e i)
  · simp only [mixedVertexEvaluation, dite_eq_left h]
    exact continuous_const
  · simp only [mixedVertexEvaluation, dite_eq_right h]
    exact (A i).toContinuousLinearEquiv.continuous.comp (continuous_apply (⟨e i, h⟩ : {q // ¬ P q}))

omit [Fintype Q] in
lemma isOpen_mixed_independent (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (A : ι → V ≃ₗ[ℝ] V) :
    IsOpen {a : {q // ¬ P q} → V | LinearIndependent ℝ (mixedVertexEvaluation P b e A a)} :=
  isOpen_setOfPred_linearIndependent.preimage (mixedVertexEvaluation_continuous P b e A)

omit [Fintype Q] in
lemma isOpen_mixed_augmented (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (A : ι → V ≃ₗ[ℝ] V) :
    IsOpen {a : {q // ¬ P q} → V | LinearIndependent ℝ
      (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a i))} := by
  apply isOpen_setOfPred_linearIndependent.preimage
  exact continuous_pi (fun i ↦ continuous_const.prodMk
    ((continuous_apply i).comp (mixedVertexEvaluation_continuous P b e A)))

lemma dense_mixed_independent (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (he : Function.Injective e) (A : ι → V ≃ₗ[ℝ] V)
    (hfixed : LinearIndependent ℝ (fun i : {i // P (e i)} ↦ A i.val (b (e i.val))))
    (hn : Fintype.card ι ≤ Module.finrank ℝ V) :
    Dense {a : {q // ¬ P q} → V | LinearIndependent ℝ (mixedVertexEvaluation P b e A a)} := by
  let e' : {i // ¬ P (e i)} → {q // ¬ P q} := fun i ↦ ⟨e i.val, i.prop⟩
  have he' : Function.Injective e' := by
    intro i j h
    exact Subtype.ext (he (congrArg Subtype.val h))
  have hc : Fintype.card {i // P (e i)} + Fintype.card {i // ¬ P (e i)} = Fintype.card ι := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.sumCompl (fun i ↦ P (e i)))
  have hh := dense_vertex_independent_extension
    (fun i : {i // P (e i)} ↦ A i.val (b (e i.val))) hfixed
    e' he' (fun i ↦ A i.val) (by rw [hc]; exact hn)
  have heval (a : {q // ¬ P q} → V) :
      mixedVertexEvaluation P b e A a ∘ Equiv.sumCompl (fun i ↦ P (e i)) =
      Sum.elim (fun i : {i // P (e i)} ↦ A i.val (b (e i.val)))
        (vertexEvaluation e' (fun i ↦ A i.val) a) := by
    funext i
    cases i with
    | inl i => simp [mixedVertexEvaluation, i.prop]
    | inr i => simp [mixedVertexEvaluation, vertexEvaluation, e', i.prop]
  have hset : {a : {q // ¬ P q} → V | LinearIndependent ℝ (mixedVertexEvaluation P b e A a)} =
      {a | LinearIndependent ℝ (Sum.elim (fun i : {i // P (e i)} ↦ A i.val (b (e i.val)))
        (vertexEvaluation e' (fun i ↦ A i.val) a))} := by
    ext a
    exact (linearIndependent_equiv' (Equiv.sumCompl (fun i ↦ P (e i))) (heval a)).symm
  rwa [hset]

lemma dense_mixed_augmented (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (he : Function.Injective e) (A : ι → V ≃ₗ[ℝ] V)
    (hfixed : LinearIndependent ℝ
      (fun i : {i // P (e i)} ↦ ((1 : ℝ), A i.val (b (e i.val)))))
    (hn : Fintype.card ι ≤ Module.finrank ℝ V + 1) :
    Dense {a : {q // ¬ P q} → V | LinearIndependent ℝ
      (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a i))} := by
  let e' : {i // ¬ P (e i)} → {q // ¬ P q} := fun i ↦ ⟨e i.val, i.prop⟩
  have he' : Function.Injective e' := by
    intro i j h
    exact Subtype.ext (he (congrArg Subtype.val h))
  have hc : Fintype.card {i // P (e i)} + Fintype.card {i // ¬ P (e i)} = Fintype.card ι := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.sumCompl (fun i ↦ P (e i)))
  have hh := dense_vertex_augmented_extension
    (fun i : {i // P (e i)} ↦ A i.val (b (e i.val))) hfixed
    e' he' (fun i ↦ A i.val) (by rw [hc]; exact hn)
  have heval (a : {q // ¬ P q} → V) :
      (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a i)) ∘ Equiv.sumCompl (fun i ↦ P (e i)) =
      (fun i ↦ ((1 : ℝ), Sum.elim (fun i : {i // P (e i)} ↦ A i.val (b (e i.val)))
        (vertexEvaluation e' (fun i ↦ A i.val) a) i)) := by
    funext i
    cases i with
    | inl i => simp [mixedVertexEvaluation, i.prop]
    | inr i => simp [mixedVertexEvaluation, vertexEvaluation, e', i.prop]
  have hset : {a : {q // ¬ P q} → V | LinearIndependent ℝ
        (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a i))} =
      {a | LinearIndependent ℝ (fun i ↦ ((1 : ℝ),
        Sum.elim (fun i : {i // P (e i)} ↦ A i.val (b (e i.val)))
          (vertexEvaluation e' (fun i ↦ A i.val) a) i))} := by
    ext a
    exact (linearIndependent_equiv' (Equiv.sumCompl (fun i ↦ P (e i))) (heval a)).symm
  rwa [hset]

end VertexEvaluation

/-- Finitely many open genericity conditions can be imposed at once. -/
lemma dense_finite_conditions {X : Type u89} {κ : Type u90} [TopologicalSpace X] [Finite κ]
    (P : κ → X → Prop) (ho : ∀ k, IsOpen {x | P k x}) (hd : ∀ k, Dense {x | P k x}) :
    Dense {x | ∀ k, P k x} := by
  have h := (Set.finite_range (fun k ↦ {x | P k x})).dense_sInter
    (by rintro _ ⟨k, rfl⟩; exact ho k) (by rintro _ ⟨k, rfl⟩; exact hd k)
  simpa only [sInter_range, mem_iInter, mem_ofPred_eq, ofPred_forall] using h

/-- Arbitrarily small generic perturbations of finitely many equivariant vertex
values, with an already generic prescribed part retained exactly. The orbit
labels and transports are abstract here; a free finite group action supplies them. -/
lemma exists_mixed_generic
    {Q : Type u91} {W : Type u92} {T₁ : Type u93} {T₂ : Type u94} [Fintype Q] [Fintype W] [Fintype T₁] [Fintype T₂]
    (J₁ : T₁ → Type u191) (J₂ : T₂ → Type u192) [∀ t, Fintype (J₁ t)] [∀ t, Fintype (J₂ t)]
    (P : Q → Prop) (b : Q → V) (e : W → Q) (A : W → V ≃ₗ[ℝ] V)
    (v₁ : ∀ t, J₁ t → W) (v₂ : ∀ t, J₂ t → W)
    (he₁ : ∀ t, Function.Injective (e ∘ v₁ t))
    (he₂ : ∀ t, Function.Injective (e ∘ v₂ t))
    (hf₁ : ∀ t, LinearIndependent ℝ
      (fun i : {i // P (e (v₁ t i))} ↦ A (v₁ t i.val) (b (e (v₁ t i.val)))))
    (hf₂ : ∀ t, LinearIndependent ℝ
      (fun i : {i // P (e (v₂ t i))} ↦ ((1 : ℝ), A (v₂ t i.val) (b (e (v₂ t i.val))))))
    (hc₁ : ∀ t, Fintype.card (J₁ t) ≤ Module.finrank ℝ V)
    (hc₂ : ∀ t, Fintype.card (J₂ t) ≤ Module.finrank ℝ V + 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : {q // ¬ P q} → V,
      (∀ w, dist (mixedVertexEvaluation P b e A a w) (A w (b (e w))) < ε) ∧
      (∀ t, LinearIndependent ℝ (fun i ↦ mixedVertexEvaluation P b e A a (v₁ t i))) ∧
      (∀ t, LinearIndependent ℝ (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a (v₂ t i)))) := by
  classical
  let C : T₁ ⊕ T₂ → ({q // ¬ P q} → V) → Prop := Sum.elim
    (fun t a ↦ LinearIndependent ℝ (fun i ↦ mixedVertexEvaluation P b e A a (v₁ t i)))
    (fun t a ↦ LinearIndependent ℝ (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a (v₂ t i))))
  have hco : ∀ t, IsOpen {a | C t a} := by
    rintro (t | t)
    · exact isOpen_mixed_independent P b (e ∘ v₁ t) (fun i ↦ A (v₁ t i))
    · exact isOpen_mixed_augmented P b (e ∘ v₂ t) (fun i ↦ A (v₂ t i))
  have hcd : ∀ t, Dense {a | C t a} := by
    rintro (t | t)
    · exact dense_mixed_independent P b (e ∘ v₁ t) (he₁ t) (fun i ↦ A (v₁ t i)) (hf₁ t) (hc₁ t)
    · exact dense_mixed_augmented P b (e ∘ v₂ t) (he₂ t) (fun i ↦ A (v₂ t i)) (hf₂ t) (hc₂ t)
  have hd := dense_finite_conditions C hco hcd
  let U : Set ({q // ¬ P q} → V) :=
    {a | dist (mixedVertexEvaluation P b e A a) (fun w ↦ A w (b (e w))) < ε}
  have hU : IsOpen U := isOpen_lt
    ((mixedVertexEvaluation_continuous P b e A).dist continuous_const) continuous_const
  have hUn : U.Nonempty := by
    refine ⟨fun q ↦ b q.val, ?_⟩
    have heq : mixedVertexEvaluation P b e A (fun q ↦ b q.val) = (fun w ↦ A w (b (e w))) := by
      funext w
      simp only [mixedVertexEvaluation]
      split_ifs <;> rfl
    change dist _ _ < ε
    rw [heq, dist_self]
    exact hε
  obtain ⟨a, hau, ha⟩ := hd.inter_open_nonempty U hU hUn
  refine ⟨a, ?_, ?_, ?_⟩
  · exact (dist_pi_lt_iff hε).mp hau
  · intro t
    exact ha (Sum.inl t)
  · intro t
    exact ha (Sum.inr t)

end SharpLiebThirring.PLParity

end
end
end
end

end OAI
