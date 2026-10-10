import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialVariation

namespace OAI

/-! Linearized polynomial operators preserve the support of the varying
field, even when the coefficients are only smooth near that support. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma tsupport_iteratedDirectional {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (w : List A) (f : A → E) :
    tsupport (iteratedDirectional w f) ⊆ tsupport f := by
  induction w with
  | nil => exact Set.Subset.rfl
  | cons v w ih => exact (tsupport_fderiv_apply_subset ℝ v).trans ih

lemma tsupport_jet (H : Base → Space) (w : List (Fin 2)) (a : Fin 4) :
    tsupport (jet H w a) ⊆ tsupport H :=
  (tsupport_iteratedDirectional (w.map coordinateVector) (fun p => H p a)).trans
    (tsupport_comp_subset (g := fun v : Space => v a) rfl H)

lemma variationLowJet_zero_of_notMem {H : Base → Space} {p : Base} (hp : p ∉ tsupport H) :
    variationLowJet H p = 0 := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    change jet H (lowWord i.1) i.2 p = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_jet H (lowWord i.1) i.2 h))

namespace Expression

lemma variation_zero_of_notMem (e : Expression) (G : Base → Space) {H : Base → Space}
    {p : Base} (hp : p ∉ tsupport H) (t : ℝ) : e.variation G H (p, t) = 0 := by
  induction e with
  | coeff c =>
    simp only [variation, variationLowJet_zero_of_notMem hp]
    change fderiv ℝ c (lowJet G p, t) (0 : LowJet × ℝ) = 0
    exact map_zero _
  | atom w a e ih =>
    have hj : jet H w a p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_jet H w a h))
    simp only [variation, hj, ih, zero_mul, mul_zero, add_zero]
  | add e f ihe ihf => simp only [variation, ihe, ihf, add_zero]

lemma tsupport_variation (e : Expression) (G H : Base → Space) (t : ℝ) :
    tsupport (fun p => e.variation G H (p, t)) ⊆ tsupport H := by
  apply closure_minimal _ (isClosed_tsupport H)
  intro p hp
  by_contra h
  exact hp (e.variation_zero_of_notMem G h t)

theorem variation_smooth_global {O : Set LowJet} (hO : IsOpen O) {U K : Set Base}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) {e : Expression}
    (he : e.SmoothCoeffs O) {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hQ : Set.MapsTo (lowJet G) U O) (hHsupp : tsupport H ⊆ K) (t : ℝ) :
    ContDiff ℝ ∞ (fun p => e.variation G H (p, t)) := by
  have hlocal := (variation_smooth hO hG hH hQ he).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hp => ⟨hp, Set.mem_univ t⟩)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ U
  · exact (hlocal p hp).contDiffAt (hU.mem_nhds hp)
  · have hpk : p ∉ K := fun hk => hp (hKU hk)
    have heq : (fun q => e.variation G H (q, t)) =ᶠ[nhds p] (fun _ => 0) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hpk] with q hq
      exact e.variation_zero_of_notMem G (fun hs => hq (hHsupp hs)) t
    exact contDiffAt_const.congr_of_eventuallyEq heq

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
