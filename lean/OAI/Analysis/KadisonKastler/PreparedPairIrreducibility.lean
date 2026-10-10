import OAI.Analysis.KadisonKastler.MatrixAveraging
import OAI.Analysis.KadisonKastler.CenterAlgebra
import OAI.Analysis.KadisonKastler.PublishedKaplansky

namespace OAI

/-! # Relative irreducibility survives a nearby common matrix algebra

Finite signed-permutation averages over increasing matrix algebras have
bounded weak operator cluster points. Such a cluster point commutes with
every stage. Relative irreducibility in the first algebra makes it scalar;
the norm ball around a relative projection in the neighbor survives the
averages and their limit. No trace, invariant mean or averaging limit is
assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem matrixUnitAverage_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖matrixUnitAverage E x‖ ≤ ‖x‖ := by
  apply norm_finiteAverage_le
  intro g
  exact (norm_unitaryConj (matrixUnitSignedRepresentation E g) x).le

private theorem matrixUnitAverage_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : VonNeumannAlgebra H) (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra) {x : H →L[ℂ] H} (hx : x ∈ M) :
    matrixUnitAverage E x ∈ M := by
  change (Fintype.card (SignedPermutation ι) : ℂ)⁻¹ •
    ∑ g : SignedPermutation ι,
      ((matrixUnitSignedRepresentation E g : H →L[ℂ] H) * x *
        star (matrixUnitSignedRepresentation E g : H →L[ℂ] H)) ∈ M
  apply M.toStarSubalgebra.smul_mem
  apply M.toStarSubalgebra.sum_mem
  intro g _
  exact M.mul_mem (M.mul_mem (hEM (matrixUnitSignedRepresentation_mem E g)) hx)
    (M.toStarSubalgebra.star_mem' (hEM (matrixUnitSignedRepresentation_mem E g)))

private theorem matrixUnitAverage_sub_fixed_norm_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (x p : H →L[ℂ] H)
    (hp : ∀ a ∈ E.algebra, a * p = p * a) :
    ‖matrixUnitAverage E x - p‖ ≤ ‖x - p‖ := by
  have he : matrixUnitAverage E x - p = finiteAverage
      (fun g : SignedPermutation ι =>
        unitaryConj (matrixUnitSignedRepresentation E g) x - p) := by
    rw [finiteAverage_sub, finiteAverage_const]
    rfl
  rw [he]
  apply norm_finiteAverage_le
  intro g
  have hfix : unitaryConj (matrixUnitSignedRepresentation E g) p = p :=
    (commute_unitary_iff_star_right_conjugate
      (matrixUnitSignedRepresentation E g).property).mp
      (hp _ (matrixUnitSignedRepresentation_mem E g))
  calc
    _ = ‖unitaryConj (matrixUnitSignedRepresentation E g) (x - p)‖ := by
      rw [unitaryConj_sub, hfix]
    _ ≤ ‖x - p‖ := (norm_unitaryConj (matrixUnitSignedRepresentation E g) (x - p)).le

/-- A bounded weak cluster point of the concrete stage averages commutes
with every fixed stage. -/
theorem matrixUnitAverage_weak_limit_commutes
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (x T : H →L[ℂ] H) {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hlim : ∀ ξ η, Tendsto (fun n => inner ℂ η (matrixUnitAverage (E n) x ξ)) l
      (𝓝 (inner ℂ η (T ξ)))) :
    ∀ n a, a ∈ (E n).algebra → a * T = T * a := by
  intro n a ha
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  have he : (fun j => inner ℂ (star a η) (matrixUnitAverage (E j) x ξ)) =ᶠ[l]
      (fun j => inner ℂ η (matrixUnitAverage (E j) x (a ξ))) := by
    filter_upwards [(eventually_ge_atTop n).filter_mono hl] with j hj
    have hc := (matrixUnitAverage_commutes (E j) x a (hmono hj ha)).eq
    have h := congrArg (fun B : H →L[ℂ] H => inner ℂ η (B ξ)) hc
    simpa only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] using h
  have hleft := (hlim ξ (star a η)).congr' he
  have hright := hlim (a ξ) η
  have h := tendsto_nhds_unique hleft hright
  simpa only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left] using h

/-- Concrete matrix-stage averages provide a scalar near every ambient
operator which commutes with those stages. -/
theorem exists_scalar_near_of_increasing_matrix_averages
    (M : VonNeumannAlgebra H)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (x p : H →L[ℂ] H) (hx : x ∈ M)
    (hp : ∀ n a, a ∈ (E n).algebra → a * p = p * a) :
    ∃ z : ℂ, ‖z • (1 : H →L[ℂ] H) - p‖ ≤ ‖x - p‖ := by
  let f : ℕ → H →L[ℂ] H := fun n => matrixUnitAverage (E n) x
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨T, _, hlim⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω f ‖x‖
    (norm_nonneg x) (fun n => matrixUnitAverage_norm_le (E n) x)
  have hTM : T ∈ M := Generator.Tracial.weak_operator_limit_mem M
    (fun n => ⟨f n, matrixUnitAverage_mem M (E n) (hEM n) hx⟩) T hlim
  obtain ⟨z, hz⟩ := hirr T hTM
    (matrixUnitAverage_weak_limit_commutes d E hmono x T hω hlim)
  refine ⟨z, ?_⟩
  rw [← hz]
  apply norm_le_of_weak_limit (l := (ω : Filter ℕ)) (fun n => f n - p) (T - p)
    (norm_nonneg (x - p)) (fun n => matrixUnitAverage_sub_fixed_norm_le (E n) x p (hp n))
  intro ξ η
  simpa only [sub_apply, inner_sub_right] using
    (hlim ξ η).sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => inner ℂ η (p ξ)) (ω : Filter ℕ) (𝓝 (inner ℂ η (p ξ))))

/-- The neighbor has no nontrivial projections in the relative commutant
when the ordinary gap is below one half. -/
theorem relative_projection_trivial_of_increasing_matrix_averages
    (M N : VonNeumannAlgebra H)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hgap : kkDistance M N < 1 / 2)
    (p : Algebra N) (hp : IsStarProjection p)
    (hcomm : ∀ n a, a ∈ (E n).algebra → a * p.val = p.val * a) :
    p = 0 ∨ p = 1 := by
  have hpp : IsStarProjection p.val := hp.map N.toStarSubalgebra.subtype
  obtain ⟨x, hx, hxp⟩ := exists_unitBall_approx (M := N) (N := M)
    ⟨p.property, hpp.norm_le⟩ (by simpa only [kkDistance_comm] using hgap)
  obtain ⟨z, hz⟩ := exists_scalar_near_of_increasing_matrix_averages M d E hmono hEM hirr
    x p.val hx.1 hcomm
  have hr : ‖x - p.val‖ < 1 / 2 := by simpa only [norm_sub_rev] using hxp
  exact (projection_eq_zero_or_one_of_near_scalar p.val hpp z (hz.trans_lt hr)).imp
    (fun h => Subtype.ext h) (fun h => Subtype.ext h)

/-- Commutation with all matrix stages extends to their generated von
Neumann algebra. -/
theorem commute_generated_of_commute_matrix_stages
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (T : H →L[ℂ] H)
    (hT : ∀ n a, a ∈ (E n).algebra → a * T = T * a) :
    ∀ a ∈ generatedVonNeumannAlgebra (⨆ n, (E n).algebra), a * T = T * a := by
  let C := StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
  have hEC : ∀ n, (E n).algebra ≤ C := by
    intro n a ha
    change a ∈ StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
    rw [StarSubalgebra.mem_centralizer_iff]
    intro t ht
    obtain rfl := Set.mem_singleton_iff.mp ht
    refine ⟨(hT n a ha).symm, ?_⟩
    have he := congrArg star (hT n (star a) ((E n).algebra.star_mem' ha))
    simpa only [star_mul, star_star] using he
  let A : StarSubalgebra ℂ (H →L[ℂ] H) := ⨆ n, (E n).algebra
  have hi : A ≤ C := iSup_le hEC
  have hc : T ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
    intro a ha
    have hh := hi ha
    change a ∈ StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) at hh
    rw [StarSubalgebra.mem_centralizer_iff] at hh
    exact (hh T (Set.mem_singleton T)).1.symm
  intro a ha
  change a ∈ (generatedVonNeumannAlgebra (⨆ n, (E n).algebra) :
    Set (H →L[ℂ] H)) at ha
  rw [generatedVonNeumannAlgebra_coe] at ha
  exact (ha T hc).symm

/-- Relative irreducibility in the first algebra passes to the neighbor
for the actual weakly generated common increasing matrix algebra. -/
theorem relative_irreducibility_of_near_increasing_matrices
    (M N : VonNeumannAlgebra H)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M,
      (∀ a ∈ generatedVonNeumannAlgebra (⨆ n, (E n).algebra), a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hgap : kkDistance M N < 1 / 2) :
    ∀ T ∈ N,
      (∀ a ∈ generatedVonNeumannAlgebra (⨆ n, (E n).algebra), a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  let R := generatedVonNeumannAlgebra (⨆ n, (E n).algebra)
  let P := vonNeumannIntersection N R.commutant
  have hstage (n : ℕ) {a : H →L[ℂ] H} (ha : a ∈ (E n).algebra) : a ∈ R :=
    subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (E n).algebra) n) ha)
  have hproj (q : Algebra P) (hq : IsStarProjection q) : q = 0 ∨ q = 1 := by
    let qN : Algebra N := ⟨q.val, q.property.1⟩
    have hqN : IsStarProjection qN := hq.map
      (StarSubalgebra.inclusion (show P.toStarSubalgebra ≤ N.toStarSubalgebra from fun _ hx => hx.1))
    have hcomm : ∀ n a, a ∈ (E n).algebra → a * qN.val = qN.val * a := by
      intro n a ha
      exact VonNeumannAlgebra.mem_commutant_iff.mp q.property.2 a (hstage n ha)
    have hm := relative_projection_trivial_of_increasing_matrix_averages M N d E hmono hEM
      (fun T hTM hTc => hirr T hTM (commute_generated_of_commute_matrix_stages d E T hTc))
      hgap qN hqN hcomm
    rcases hm with h | h
    · left
      apply Subtype.ext
      change qN.val = 0
      exact congrArg Subtype.val h
    · right
      apply Subtype.ext
      change qN.val = 1
      exact congrArg Subtype.val h
  intro T hTN hTR
  let a : Algebra P := ⟨T, hTN, VonNeumannAlgebra.mem_commutant_iff.mpr hTR⟩
  let p : Generator.Tracial.AlgebraProjection P := ⟨1, IsStarProjection.one _⟩
  have hmin : ∀ q : Generator.Tracial.AlgebraProjection P, q ≤ p → q.val = 0 ∨ q.val = p.val := by
    intro q _
    exact hproj q.val q.property
  obtain ⟨z, hz⟩ := Generator.Tracial.corner_scalar_of_projections p hmin a
    (by change 1 * a = a; exact one_mul a) (by change a * 1 = a; exact mul_one a)
  exact ⟨z, congrArg Subtype.val hz⟩

end

end KadisonKastler

end OAI
