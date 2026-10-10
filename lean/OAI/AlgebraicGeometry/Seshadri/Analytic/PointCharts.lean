import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Analytic.PolynomialCharts

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {F S ι σ : Type*} [CommRing F] [CommRing S] [Algebra F S]

def presentationPoint (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) : S →ₐ[F] F :=
  (Ideal.Quotient.liftₐ P.ker (aeval x) (by
    change P.ker ≤ RingHom.ker (aeval x).toRingHom
    rw [← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change aeval x (P.relation i) = 0
    simpa using hx i)).comp (P.quotientEquiv.restrictScalars F).symm.toAlgHom

lemma presentationPoint_apply (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) (s : S) :
    presentationPoint P x hx s = eval x (P.σ s) := by
  simp [presentationPoint]

lemma presentationPoint_aeval (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) (f : MvPolynomial ι F) :
    presentationPoint P x hx (aeval P.val f) = eval x f := by
  have he : (P.quotientEquiv.restrictScalars F).symm (aeval P.val f) =
      Ideal.Quotient.mk P.ker f := by
    apply (P.quotientEquiv.restrictScalars F).injective
    simp
  simp only [presentationPoint, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [he]
  simp

lemma presentationPoint_val (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) (i : ι) :
    presentationPoint P x hx (P.val i) = x i := by
  simpa using presentationPoint_aeval P x hx (X i)

lemma evaluation_relations (P : Algebra.Presentation F S ι σ) (ρ : S →ₐ[F] F) (i : σ) :
    eval (fun a => ρ (P.val a)) (P.relation i) = 0 := by
  have he : aeval (fun a => ρ (P.val a)) = ρ.comp (aeval P.val) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp
  change aeval (fun a => ρ (P.val a)) (P.relation i) = 0
  rw [he]
  simp

lemma presentationPoint_at_point (P : Algebra.Presentation F S ι σ) (ρ : S →ₐ[F] F) :
    presentationPoint P (fun a => ρ (P.val a)) (evaluation_relations P ρ) = ρ := by
  ext s
  obtain ⟨f, rfl⟩ := P.aeval_val_surjective s
  rw [presentationPoint_aeval]
  change aeval (fun a => ρ (P.val a)) f = _
  rw [← MvPolynomial.comp_aeval]
  rfl

end

noncomputable section
open MvPolynomial
open scoped BigOperators Matrix ContDiff
variable {F ι σ S : Type*} [RCLike F] [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra F S]

theorem exists_analytic_zero_chart
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ γ : ({i : ι // i ∉ Set.range P.map} → F) → (ι → F),
      γ (fun i => ρ (P.val i.val)) = (fun a => ρ (P.val a)) ∧
      AnalyticAt F γ (fun i => ρ (P.val i.val)) ∧
      ∀ᶠ z in nhds (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)),
        (∀ i, eval (γ z) (P.relation i) = 0) ∧ (∀ i, γ z i.val = z i) := by
  obtain ⟨ψ, hbase, han, hinv⟩ := exists_analytic_augmented_inverse P ρ
  have he : augmentedPolynomial P (fun a => ρ (P.val a)) =
      (0, fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)) := by
    ext a
    · exact evaluation_relations P.toPresentation ρ a
    · rfl
  rw [he] at hbase han hinv
  let γ : ({i : ι // i ∉ Set.range P.map} → F) → (ι → F) := fun z => ψ (0, z)
  have hz : AnalyticAt F (fun z : ({i : ι // i ∉ Set.range P.map} → F) =>
      ((0 : σ → F), z)) (fun i => ρ (P.val i.val)) :=
    analyticAt_const.prod analyticAt_id
  refine ⟨γ, hbase, han.comp hz, ?_⟩
  filter_upwards [hz.continuousAt.eventually hinv] with z hz'
  constructor
  · intro i
    exact congrArg (fun y => y.1 i) hz'
  · intro i
    exact congrArg (fun y => y.2 i) hz'

theorem exists_analytic_point_chart
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ q : ({i : ι // i ∉ Set.range P.map} → F) → (S →ₐ[F] F),
      q (fun i => ρ (P.val i.val)) = ρ ∧
      (∀ s : S, AnalyticAt F (fun z => q z s) (fun i => ρ (P.val i.val))) ∧
      ∀ᶠ z in nhds (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)),
        ∀ i, q z (P.val i.val) = z i := by
  classical
  obtain ⟨γ, hbase, han, hrel⟩ := exists_analytic_zero_chart P ρ
  let q : ({i : ι // i ∉ Set.range P.map} → F) → (S →ₐ[F] F) := fun z =>
    if h : ∀ i, eval (γ z) (P.relation i) = 0 then
      presentationPoint P.toPresentation (γ z) h else ρ
  have heq : ∀ᶠ z in nhds (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)),
      ∀ s, q z s = eval (γ z) (P.σ s) := by
    filter_upwards [hrel] with z hz
    intro s
    simp only [q, dite_eq_left hz.1]
    exact presentationPoint_apply P.toPresentation (γ z) hz.1 s
  refine ⟨q, ?_, ?_, ?_⟩
  · have hzero : ∀ i, eval (γ (fun i => ρ (P.val i.val))) (P.relation i) = 0 := by
      rw [hbase]
      exact evaluation_relations P.toPresentation ρ
    simp only [q, dite_eq_left hzero]
    simpa only [hbase] using presentationPoint_at_point P.toPresentation ρ
  · intro s
    have h := (analyticAt_polynomial_eval (P.σ s) _).comp han
    apply h.congr
    filter_upwards [heq] with z hz
    exact (hz s).symm
  · filter_upwards [hrel] with z hz
    intro i
    simp only [q, dite_eq_left hz.1]
    rw [presentationPoint_val]
    exact hz.2 i

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped Topology ContDiff
open MvPolynomial
variable {ι σ S : Type*} [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra ℂ S]

theorem exists_binary_point_chart
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : {i : ι // i ∉ Set.range P.map} ≃ Fin 2) (ρ : S →ₐ[ℂ] ℂ) :
    ∃ q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ), q 0 = ρ ∧
      (∀ s : S, AnalyticAt ℂ (fun z => q z s) 0) ∧
      ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
        q z (P.val (e.symm i)) = ρ (P.val (e.symm i)) +
          (if i = 0 then z.2 else z.1) := by
  obtain ⟨q₀, hbase, han, hc⟩ := exists_analytic_point_chart P ρ
  let α (z : ℂ × ℂ) (i : {i : ι // i ∉ Set.range P.map}) :=
    ρ (P.val i) + (if e i = 0 then z.2 else z.1)
  have hα : AnalyticAt ℂ α 0 := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.add analyticAt_const
    by_cases h : e i = 0
    · simpa only [ite_eq_left h] using (analyticAt_snd (𝕜 := ℂ) (p := (0 : ℂ × ℂ)))
    · simpa only [ite_eq_right h] using (analyticAt_fst (𝕜 := ℂ) (p := (0 : ℂ × ℂ)))
  have hα₀ : α 0 = (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i)) := by
    ext i
    simp [α]
  refine ⟨fun z => q₀ (α z), ?_, ?_, ?_⟩
  · change q₀ (α 0) = ρ
    rw [hα₀, hbase]
  · intro s
    have h : AnalyticAt ℂ (fun z => q₀ z s) (α 0) := by
      rw [hα₀]
      exact han s
    exact h.comp hα
  · have hcp : ∀ᶠ z in 𝓝 (α 0), ∀ i, q₀ z (P.val i.val) = z i := by
      rw [hα₀]
      exact hc
    have hpull := hα.continuousAt.eventually hcp
    filter_upwards [hpull] with z hz
    intro i
    simpa [α] using hz (e.symm i)

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
