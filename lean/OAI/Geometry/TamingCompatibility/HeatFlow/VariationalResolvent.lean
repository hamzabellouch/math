import Mathlib

namespace OAI


noncomputable section
open scoped RealInnerProductSpace

namespace TamingCompatibility.Fredholm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def nullspace (K : H →L[ℝ] H) : Submodule ℝ H := (1 - K).ker

omit [CompleteSpace H] in
lemma mem_nullspace (K : H →L[ℝ] H) (x : H) : x ∈ nullspace K ↔ K x = x := by
  change x - K x = 0 ↔ K x = x
  exact sub_eq_zero.trans eq_comm

instance (K : H →L[ℝ] H) : _root_.IsClosed (nullspace K : Set H) := (1 - K).isClosed_ker

instance (K : H →L[ℝ] H) : CompleteSpace (nullspace K) := _root_.IsClosed.completeSpace_coe

omit [CompleteSpace H] in

lemma map_orthogonal_nullspace (K : H →L[ℝ] H) (hK : K.toLinearMap.IsSymmetric)
    (x : H) (hx : x ∈ (nullspace K)ᗮ) : K x ∈ (nullspace K)ᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  change ⟪y, K.toLinearMap x⟫ = 0
  rw [← hK y x]
  change ⟪K y, x⟫ = 0
  rw [(mem_nullspace K y).mp hy]
  exact hx y hy

omit [CompleteSpace H] in

theorem finiteDimensional_nullspace (K : H →L[ℝ] H) (hK : IsCompactOperator K) :
    FiniteDimensional ℝ (nullspace K) := by
  have hinv : ∀ x ∈ nullspace K, K.toLinearMap x ∈ nullspace K := by
    intro x hx
    simpa only [ContinuousLinearMap.coe_coe, (mem_nullspace K x).mp hx] using hx
  have hc := hK.restrict hinv (1 - K).isClosed_ker
  have heq : K.toLinearMap.restrict hinv = LinearMap.id := by
    ext x
    exact (mem_nullspace K x).mp x.2
  rw [heq] at hc
  exact isCompactOperator_id_iff_finiteDimensional.mp hc

theorem exists_inverse_on_complement (K : H →L[ℝ] H)
    (hK : IsCompactOperator K) (hs : K.toLinearMap.IsSymmetric) :
    ∃ U : ((nullspace K)ᗮ →L[ℝ] (nullspace K)ᗮ),
      (1 - K.restrict (map_orthogonal_nullspace K hs)) * U = 1 ∧
      U * (1 - K.restrict (map_orthogonal_nullspace K hs)) = 1 := by
  let V := (nullspace K)ᗮ
  let A : V →L[ℝ] V := K.restrict (map_orthogonal_nullspace K hs)
  have hAc : IsCompactOperator A :=
    hK.restrict (map_orthogonal_nullspace K hs) (nullspace K).isClosed_orthogonal
  have hne : ¬ Module.End.HasEigenvalue A.toLinearMap 1 := by
    intro he
    obtain ⟨x, hx⟩ := he.exists_hasEigenvector
    have hxx : K (x : H) = x := by
      have ht := congrArg (fun v : V => (v : H)) hx.apply_eq_smul
      change K (x : H) = (1 : ℝ) • (x : H) at ht
      simpa only [one_smul] using ht
    have hxN : (x : H) ∈ nullspace K := (mem_nullspace K x).mpr hxx
    have hzero : (x : H) = 0 := by
      have hi := (Submodule.mem_orthogonal (nullspace K) x).mp x.2 x hxN
      exact inner_self_eq_zero.mp hi
    exact hx.2 (Subtype.ext hzero)
  have hr : (1 : ℝ) ∈ resolventSet ℝ A :=
    (hAc.hasEigenvalue_or_mem_resolventSet one_ne_zero).resolve_left hne
  have hu : IsUnit (1 - A) := by
    simpa only [spectrum.mem_resolventSet_iff, map_one] using hr
  obtain ⟨u, hu⟩ := hu
  refine ⟨↑u⁻¹, ?_, ?_⟩
  · change (1 - A) * ↑u⁻¹ = 1
    rw [← hu]
    exact u.val_inv
  · change ↑u⁻¹ * (1 - A) = 1
    rw [← hu]
    exact u.inv_val

theorem exists_generalized_inverse (K : H →L[ℝ] H)
    (hK : IsCompactOperator K) (hs : K.toLinearMap.IsSymmetric) :
    ∃ G : H →L[ℝ] H,
      (1 - K) * G = 1 - (nullspace K).starProjection ∧
      G * (1 - K) = 1 - (nullspace K).starProjection ∧
      (∀ x, G x ∈ (nullspace K)ᗮ) ∧
      (∀ x ∈ nullspace K, G x = 0) := by
  obtain ⟨U, hU, hU'⟩ := exists_inverse_on_complement K hK hs
  let N := nullspace K
  let V := Nᗮ
  let A : V →L[ℝ] V := K.restrict (map_orthogonal_nullspace K hs)
  let G : H →L[ℝ] H := V.subtypeL ∘L U ∘L V.orthogonalProjectionOnto
  have hGmem (x : H) : G x ∈ V := (U (V.orthogonalProjectionOnto x)).2
  have hleft (x : H) : (1 - K) (G x) = V.starProjection x := by
    have hv := congrArg (fun T : V →L[ℝ] V => (T (V.orthogonalProjectionOnto x) : H)) hU
    change (U (V.orthogonalProjectionOnto x) : H) -
      K (U (V.orthogonalProjectionOnto x) : H) = (V.orthogonalProjectionOnto x : H) at hv
    exact hv
  have hGzero (x : H) (hx : x ∈ N) : G x = 0 := by
    have hz : V.orthogonalProjectionOnto x = 0 :=
      V.orthogonalProjectionOnto_apply_of_mem_orthogonal (N.le_orthogonal_orthogonal hx)
    change (U (V.orthogonalProjectionOnto x) : H) = 0
    rw [hz, map_zero]
    rfl
  have hTmem (x : H) : (1 - K) x ∈ V := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    change ⟪y, x - K x⟫ = 0
    rw [inner_sub_right]
    have hxy : ⟪y, K x⟫ = ⟪y, x⟫ := by
      change ⟪y, K.toLinearMap x⟫ = _
      rw [← hs y x]
      change ⟪K y, x⟫ = _
      rw [(mem_nullspace K y).mp hy]
    rw [hxy, sub_self]
  have hTproj (x : H) : (1 - K) (V.starProjection x) = (1 - K) x := by
    rw [N.starProjection_orthogonal_val, map_sub]
    have hz : (1 - K) (N.starProjection x) = 0 := (N.orthogonalProjectionOnto x).2
    rw [hz, sub_zero]
  have hright (x : H) : G ((1 - K) x) = V.starProjection x := by
    let y := G ((1 - K) x) - V.starProjection x
    have hyV : y ∈ V := V.sub_mem (hGmem _) (V.orthogonalProjectionOnto x).2
    have hyN : y ∈ N := by
      show (1 - K) y = 0
      rw [map_sub, hleft, hTproj,
        V.starProjection_eq_self_iff.mpr (hTmem x), sub_self]
    have hi := (Submodule.mem_orthogonal N y).mp hyV y hyN
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hi)
  refine ⟨G, ?_, ?_, hGmem, hGzero⟩
  · ext x
    change (1 - K) (G x) = x - N.starProjection x
    rw [hleft, N.starProjection_orthogonal_val]
  · ext x
    change G ((1 - K) x) = x - N.starProjection x
    rw [hright, N.starProjection_orthogonal_val]

end TamingCompatibility.Fredholm

namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

def energy (i : V →L[ℝ] H) (D : V →L[ℝ] Z) : V →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp i i + (innerSL ℝ).bilinearComp D D

omit [CompleteSpace V] [CompleteSpace H] in
@[simp] lemma energy_apply (i : V →L[ℝ] H) (D : V →L[ℝ] Z) (u v : V) :
    energy i D u v = ⟪i u, i v⟫ + ⟪D u, D v⟫ := rfl

def weakSolution (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) : H →L[ℝ] V :=
  hc.continuousLinearEquivOfBilin.symm.toContinuousLinearMap ∘L i.adjoint

lemma weakSolution_identity (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) (v : V) :
    ⟪i (weakSolution i D hc f), i v⟫ + ⟪D (weakSolution i D hc f), D v⟫ = ⟪f, i v⟫ := by
  rw [← energy_apply, ← hc.continuousLinearEquivOfBilin_apply]
  simp only [weakSolution, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  exact i.adjoint_inner_left v f

def resolvent (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) : H →L[ℝ] H := i ∘L weakSolution i D hc

lemma resolvent_compact (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (hi : IsCompactOperator i) :
    IsCompactOperator (resolvent i D hc) := hi.comp_clm _

lemma resolvent_symmetric (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) : (resolvent i D hc).toLinearMap.IsSymmetric := by
  intro f g
  have hfg := weakSolution_identity i D hc f (weakSolution i D hc g)
  have hgf := weakSolution_identity i D hc g (weakSolution i D hc f)
  change ⟪i (weakSolution i D hc f), g⟫ = ⟪f, i (weakSolution i D hc g)⟫
  calc
    _ = ⟪g, i (weakSolution i D hc f)⟫ := real_inner_comm _ _
    _ = _ := by
      rw [← hgf, ← hfg]
      congr 1 <;> exact real_inner_comm _ _

lemma resolvent_nonnegative (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) : 0 ≤ ⟪f, resolvent i D hc f⟫ := by
  change 0 ≤ ⟪f, i (weakSolution i D hc f)⟫
  rw [← weakSolution_identity i D hc f (weakSolution i D hc f)]
  exact add_nonneg (real_inner_self_nonneg) (real_inner_self_nonneg)

lemma resolvent_norm_le (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) : ‖resolvent i D hc f‖ ≤ ‖f‖ := by
  have h := weakSolution_identity i D hc f (weakSolution i D hc f)
  have hle := real_inner_le_norm f (i (weakSolution i D hc f))
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  change ‖i (weakSolution i D hc f)‖ ≤ ‖f‖
  by_cases hz : i (weakSolution i D hc f) = 0
  · simp [hz]
  · have hp : 0 < ‖i (weakSolution i D hc f)‖ := norm_pos_iff.mpr hz
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [sq_nonneg ‖D (weakSolution i D hc f)‖]

lemma mem_nullspace_iff (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) :
    f ∈ Fredholm.nullspace (resolvent i D hc) ↔ ∃ u : V, i u = f ∧ D u = 0 := by
  rw [Fredholm.mem_nullspace]
  constructor
  · intro hf
    refine ⟨weakSolution i D hc f, hf, ?_⟩
    have he := weakSolution_identity i D hc f (weakSolution i D hc f)
    change i (weakSolution i D hc f) = f at hf
    rw [hf] at he
    have hz : ⟪D (weakSolution i D hc f), D (weakSolution i D hc f)⟫ = 0 := by linarith
    exact inner_self_eq_zero.mp hz
  · rintro ⟨u, rfl, hu⟩
    have he : weakSolution i D hc (i u) = u := by
      apply hc.continuousLinearEquivOfBilin.injective
      apply ext_inner_right ℝ
      intro v
      rw [hc.continuousLinearEquivOfBilin_apply,
        hc.continuousLinearEquivOfBilin_apply, energy_apply, energy_apply,
        weakSolution_identity, hu, inner_zero_left, add_zero]
    change i (weakSolution i D hc (i u)) = i u
    rw [he]

theorem exists_energy_inverse (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (hi : IsCompactOperator i) :
    let N := Fredholm.nullspace (resolvent i D hc)
    FiniteDimensional ℝ N ∧ ∃ G : H →L[ℝ] V,
      (∀ f v, ⟪D (G f), D v⟫ = ⟪f - N.starProjection f, i v⟫) ∧
      (∀ f, i (G f) ∈ Nᗮ) ∧ (∀ f ∈ N, G f = 0) := by
  dsimp only
  let K := resolvent i D hc
  let N := Fredholm.nullspace K
  have hKc := resolvent_compact i D hc hi
  have hKs := resolvent_symmetric i D hc
  refine ⟨Fredholm.finiteDimensional_nullspace K hKc, ?_⟩
  obtain ⟨U, hleft, _, hmem, hzero⟩ := Fredholm.exists_generalized_inverse K hKc hKs
  refine ⟨weakSolution i D hc ∘L U, ?_, ?_, ?_⟩
  · intro f v
    have hw := weakSolution_identity i D hc (U f) v
    have hu := congrArg (fun A : H →L[ℝ] H => A f) hleft
    change U f - K (U f) = f - N.starProjection f at hu
    rw [← hu, inner_sub_left]
    change ⟪D (weakSolution i D hc (U f)), D v⟫ = ⟪U f, i v⟫ - ⟪i (weakSolution i D hc (U f)), i v⟫
    linarith
  · intro f
    exact Fredholm.map_orthogonal_nullspace K hKs (U f) (hmem f)
  · intro f hf
    change weakSolution i D hc (U f) = 0
    rw [hzero f hf, map_zero]

end TamingCompatibility.Variational

end

end OAI
