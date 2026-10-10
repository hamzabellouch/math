import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.FalconerCompletion.Graphs.RetainedCenterTests
import OAI.MeasureTheory.FalconerCompletion.Sphere.SpherePlaneWave2

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem source_graph_degrees {sig c₀ Ccap : ℝ} (hsig : 0 < sig)
    (hc₀ : 0 ≤ c₀) (hCcap : 0 ≤ Ccap) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (ρ₁ ρ₂ : Measure (EuclideanSpace ℝ (Fin d))) (A₁ A₂ : ℕ → ℝ)
      (C : ℝ) (J i₁ i₂ a g₁ g₂ p : ℕ) (X Y : CellPath d) (A B : Finset (CellPath d))
      (ηv ηw : EuclideanSpace ℝ (Fin d) → ℝ)
      (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
      (v w : EuclideanSpace ℝ (Fin d)),
    a ≤ g₁ → a ≤ g₂ → g₁ ≤ p → g₂ ≤ p →
    (g₁:ℝ) ≤ (a:ℝ)+2*sig*N → (g₂:ℝ) ≤ (a:ℝ)+2*sig*N →
    0 < J → i₁ ≤ J → i₂ ≤ J → ‖v‖=1 → ‖w‖=1 →
    (∀ u, ‖u‖=1 → ηv u ≠ 0 → dist v u ≤ Ccap*graphCapScale N a p c₀ sig) →
    (∀ u, ‖u‖=1 → ηw u ≠ 0 → dist w u ≤ Ccap*graphCapScale N a p c₀ sig) →
    ImposesParallelTest ρ₁ g₁ p (testWidth N J i₁ p sig)
      (((2:ℝ)^N)^(height A₁ g₁ p+C*sig)) b →
    ImposesParallelTest ρ₂ g₂ p (testWidth N J i₂ p sig)
      (((2:ℝ)^N)^(height A₂ g₂ p+C*sig)) c →
    let Sv := eligibleCells ρ₁ a p X ηv b
    let Sw := eligibleCells ρ₁ a p X ηw b
    let Tv := eligibleCells ρ₂ a p Y ηv c
    let Tw := eligibleCells ρ₂ a p Y ηw c
    let τ := graphTolerance N p sig
    let D := ((2:ℝ)^N)^(min (height A₁ a p) (height A₂ a p)+(C+32*(d:ℝ)+1)*sig)
    (∀ row,
      (((A.product B).filter (retainedHGraph Sv Tw v w τ row)).card : ℝ) ≤ D ∧
      (((A.product B).filter (retainedHFGraph Sv Sw Tv Tw v w τ row)).card : ℝ) ≤ D) ∧
    (∀ col,
      (((A.product B).filter (fun row => retainedHGraph Sv Tw v w τ row col)).card : ℝ) ≤ D ∧
      (((A.product B).filter (fun row => retainedHFGraph Sv Sw Tv Tw v w τ row col)).card : ℝ) ≤ D) := by
  obtain ⟨N₀,hN₀⟩ := graph_eventually_large (d:=d) hsig Ccap
  refine ⟨N₀,?_⟩
  intro N hN ρ₁ ρ₂ A₁ A₂ C J i₁ i₂ a g₁ g₂ p X Y A B ηv ηw b c v w
    hag₁ hag₂ hg₁p hg₂p hanchor₁ hanchor₂ hJ hi₁ hi₂ hv hw hcapv hcapw htest₁ htest₂
  obtain ⟨hlarge₁,hlarge₂⟩ := hN₀ N hN
  have hδ : 0 ≤ Ccap*graphCapScale N a p c₀ sig :=
    mul_nonneg hCcap (graphCapScale_nonneg hc₀)
  have hτ : 0 ≤ graphTolerance N p sig := by rw [graphTolerance_eq]; positivity
  have hW₁ := graph_source_width (c₀:=c₀) (p:=p) hsig.le hCcap hag₁ hJ hi₁ hlarge₂
  have hW₂ := graph_source_width (c₀:=c₀) (p:=p) hsig.le hCcap hag₂ hJ hi₂ hlarge₂
  have hdeg := eligibleGraphDegrees ρ₁ ρ₂ a g₁ g₂ p X Y A B ηv ηw b c v w
    (Ccap*graphCapScale N a p c₀ sig) (graphTolerance N p sig)
    (testWidth N J i₁ p sig) (testWidth N J i₂ p sig)
    (((2:ℝ)^N)^(height A₁ g₁ p+C*sig)) (((2:ℝ)^N)^(height A₂ g₂ p+C*sig))
    hag₁ hag₂ hg₁p hg₂p hv hw hδ hτ (by positivity) (by positivity)
    hW₁ hW₂ hcapv hcapw htest₁ htest₂
  have hscale := graph_source_degree_scale_absorb (C:=C) A₁ A₂ hsig.le hag₁ hag₂ hg₁p hg₂p
    hanchor₁ hanchor₂ hlarge₁
  exact ⟨fun row => ⟨((hdeg.1 row).1).trans hscale,((hdeg.1 row).2).trans hscale⟩,
    fun col => ⟨((hdeg.2 col).1).trans hscale,((hdeg.2 col).2).trans hscale⟩⟩

end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
variable {V : Type*}

theorem zero_cap_energy_transform [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ σ : Measure V)
    [IsFiniteMeasure μ] [IsFiniteMeasure σ]
    (η : V → ℝ) (b : V → V → ℂ)
    (hη : Measurable η) (hb : Measurable (Function.uncurry b))
    {P B : ℝ} (hP : 0 ≤ P) (_hB : 0 ≤ B)
    (hη0 : ∀ᵐ w ∂σ, 0 ≤ η w) (hηP : ∀ᵐ w ∂σ, η w ≤ P)
    (hbB : ∀ᵐ w ∂σ, ∀ x, ‖b x w‖ ≤ B)
    (hzero : (∫ x, ∫ w, η w * ‖b x w‖^2 ∂σ ∂μ)=0) :
    ∀ᵐ w ∂σ, η w=0 ∨ ∀ r, sourceAngularTransformND μ univ 1 b r w=0 := by
  let f : V×V → ℝ := fun z => η z.2*‖b z.1 z.2‖^2
  have hfm : Measurable f := (hη.comp measurable_snd).mul (hb.norm.pow_const 2)
  have hfn : 0 ≤ᵐ[μ.prod σ] f := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hη0] with z hz
    exact mul_nonneg hz (sq_nonneg _)
  have hfi : Integrable f (μ.prod σ) := by
    apply Integrable.of_bound hfm.aestronglyMeasurable (P*B^2)
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hη0,Measure.quasiMeasurePreserving_snd.ae hηP,Measure.quasiMeasurePreserving_snd.ae hbB] with z hn hp hb
    change ‖η z.2*‖b z.1 z.2‖^2‖ ≤ P*B^2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (sq_nonneg _))]
    exact mul_le_mul hp (pow_le_pow_left₀ (norm_nonneg _) (hb z.1) 2) (sq_nonneg _) hP
  have hfz : f =ᵐ[μ.prod σ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae hfn hfi).mp
    rw [integral_prod _ hfi]
    exact hzero
  have hswap : ∀ᵐ w ∂σ, ∀ᵐ x ∂μ, η w*‖b x w‖^2=0 := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod hfz)
    exact hfm (measurableSet_singleton 0)
  filter_upwards [hswap] with w hw
  by_cases he : η w=0
  · exact Or.inl he
  right
  intro r
  unfold sourceAngularTransformND
  simp only [inv_one,one_smul,Measure.restrict_univ]
  apply integral_eq_zero_of_ae
  filter_upwards [hw] with x hx
  have hn : ‖b x w‖^2=0 := (mul_eq_zero.mp hx).resolve_left he
  have hz : b x w=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  simp [hz]

lemma cap_energy_nonneg [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ σ : Measure V) (η : V → ℝ) (b : V → V → ℂ)
    (hη : ∀ᵐ w ∂σ, 0 ≤ η w) :
    0 ≤ ∫ x, ∫ w, η w*‖b x w‖^2 ∂σ ∂μ := by
  apply integral_nonneg
  intro x
  apply integral_nonneg_of_ae
  filter_upwards [hη] with w hw
  exact mul_nonneg hw (sq_nonneg _)

theorem nonpositive_cap_pair_zero [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ σ : Measure V)
    [IsFiniteMeasure μ] [IsFiniteMeasure σ]
    (η : V → ℝ) (b : V → V → ℂ)
    (hη : Measurable η) (hb : Measurable (Function.uncurry b))
    {P B : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hη0 : ∀ᵐ w ∂σ, 0 ≤ η w) (hηP : ∀ᵐ w ∂σ, η w ≤ P)
    (hbB : ∀ᵐ w ∂σ, ∀ x, ‖b x w‖ ≤ B)
    (hzero : ¬0 < (∫ x, ∫ w, η w * ‖b x w‖^2 ∂σ ∂μ))
    (θ W : V → ℂ) (r : ℝ) :
    (∫ w, (η w:ℂ)*θ w*sourceAngularTransformND μ univ 1 b r w*conj (W w) ∂σ)=0 ∧
    (∫ w, (η w:ℂ)*θ w*W w*conj (sourceAngularTransformND μ univ 1 b r w) ∂σ)=0 := by
  have hz := zero_cap_energy_transform μ σ η b hη hb hP hB hη0 hηP hbB
    (le_antisymm (not_lt.mp hzero) (cap_energy_nonneg μ σ η b hη0))
  constructor <;> apply integral_eq_zero_of_ae <;> filter_upwards [hz] with w hw
  · rcases hw with hw | hw <;> simp [hw]
  · rcases hw with hw | hw <;> simp [hw]

end CurrentFalconer
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace Attempt4Near
open Set MeasureTheory
open scoped ENNReal ComplexConjugate
variable {V : Type*} [MeasurableSpace V]

noncomputable def sourceAngularMomentND (μ : Measure V) (U : ℝ × V → ℂ) (r : ℝ) : ℝ :=
  ∫ w, ‖U (r,w)‖^2 ∂μ

noncomputable def sourceAngularHND (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (U W : ℝ × V → ℂ) : ℝ :=
  (2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
    ∫ r, Ψ (r/(2:ℝ)^v)*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r

noncomputable def sourceAngularHFND (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (ψ : V → ℂ) (U W : ℝ × V → ℂ) : ℝ :=
  (2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
    ∫ r, Ψ (r/(2:ℝ)^v)*‖∫ w, ψ w*U (r,w)*conj (W (r,w)) ∂μ‖^2

lemma graph_radial_normalizationND {Ω : ℝ} (hΩ : 0 < Ω) (Ψ f : ℝ → ℝ) :
    Ω⁻¹*(∫ r, Ψ (r/Ω)*f r) = ∫ u, Ψ u*f (Ω*u) := by
  have h := Measure.integral_comp_mul_left (fun r => Ψ (r/Ω)*f r) Ω
  simp only [abs_of_pos (inv_pos.mpr hΩ),smul_eq_mul] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_div_cancel_left₀ u hΩ.ne']

lemma sourceAngularHND_normalized (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (U W : ℝ × V → ℂ) :
    sourceAngularHND d μ a v Ψ U W = (2:ℝ)^((d:ℝ)*(v-a))*
      ∫ u, Ψ u*sourceAngularMomentND μ U ((2:ℝ)^v*u)*sourceAngularMomentND μ W ((2:ℝ)^v*u) := by
  dsimp [sourceAngularHND]
  rw [mul_assoc]
  congr 1
  simpa only [mul_assoc] using graph_radial_normalizationND (by positivity : (0:ℝ)<(2:ℝ)^v)
    Ψ (fun r => sourceAngularMomentND μ U r*sourceAngularMomentND μ W r)

lemma sourceAngularHFND_normalized (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (ψ : V → ℂ) (U W : ℝ × V → ℂ) :
    sourceAngularHFND d μ a v Ψ ψ U W = (2:ℝ)^((d:ℝ)*(v-a))*
      ∫ u, Ψ u*‖∫ w, ψ w*U ((2:ℝ)^v*u,w)*conj (W ((2:ℝ)^v*u,w)) ∂μ‖^2 := by
  dsimp [sourceAngularHFND]
  rw [mul_assoc,graph_radial_normalizationND (by positivity : (0:ℝ)<(2:ℝ)^v)]

lemma sourceAngularMomentND_measurable (μ : Measure V) [SFinite μ]
    {U : ℝ × V → ℂ} (hU : Measurable U) : Measurable (sourceAngularMomentND μ U) :=
  (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

lemma sourceAngularMomentND_nonneg (μ : Measure V) (U : ℝ × V → ℂ) (r : ℝ) :
    0 ≤ sourceAngularMomentND μ U r := integral_nonneg (fun _ => sq_nonneg _)

lemma sourceAngularMomentND_bound (μ : Measure V) [IsFiniteMeasure μ]
    (U : ℝ × V → ℂ) {C : ℝ} (r : ℝ) (hb : ∀ᵐ w ∂μ, ‖U (r,w)‖ ≤ C) :
    sourceAngularMomentND μ U r ≤ C^2*μ.real univ := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hb] with w hw
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hw 2

lemma angular_square_integrableND (μ : Measure V) [IsFiniteMeasure μ]
    {f : V → ℂ} (hf : Measurable f) {C : ℝ} (hb : ∀ᵐ w ∂μ, ‖f w‖ ≤ C) :
    Integrable (fun w => ‖f w‖^2) μ := by
  apply Integrable.of_bound (hf.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards [hb] with w hw
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hw 2

lemma graph_weighted_moments_integrableND (μ : Measure V) [IsFiniteMeasure μ]
    {U W : ℝ × V → ℂ} (hU : Measurable U) (hW : Measurable W)
    {C D : ℝ} (hUbound : ∀ r, ∀ᵐ w ∂μ, ‖U (r,w)‖ ≤ C)
    (hWbound : ∀ r, ∀ᵐ w ∂μ, ‖W (r,w)‖ ≤ D)
    {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ) :
    Integrable (fun r => Ψ r*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r) := by
  apply (hΨ.norm.mul_const ((C^2*μ.real univ)*(D^2*μ.real univ))).mono'
    ((hΨ.aestronglyMeasurable.mul (sourceAngularMomentND_measurable μ hU).aestronglyMeasurable).mul
      (sourceAngularMomentND_measurable μ hW).aestronglyMeasurable)
  filter_upwards with r
  change ‖Ψ r*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r‖ ≤ _
  rw [norm_mul,norm_mul,Real.norm_eq_abs (sourceAngularMomentND μ U r),
    Real.norm_eq_abs (sourceAngularMomentND μ W r),
    abs_of_nonneg (sourceAngularMomentND_nonneg μ U r),
    abs_of_nonneg (sourceAngularMomentND_nonneg μ W r),mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (sourceAngularMomentND_bound μ U r (hUbound r))
    (sourceAngularMomentND_bound μ W r (hWbound r)) (sourceAngularMomentND_nonneg μ W r)
      (by positivity)) (norm_nonneg _)

lemma sourceAngularMomentND_pair (μ : Measure V) [SFinite μ]
    (U W : ℝ × V → ℂ) (r : ℝ) :
    (∫ w : V × V, ‖U (r,w.1)*W (r,w.2)‖^2 ∂μ.prod μ) =
      sourceAngularMomentND μ U r*sourceAngularMomentND μ W r := by
  simp_rw [norm_mul,mul_pow]
  exact integral_prod_mul (fun w => ‖U (r,w)‖^2) (fun w => ‖W (r,w)‖^2)

end Attempt4Near
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace Attempt4Near
open scoped BigOperators ComplexConjugate
theorem finset_bipartite_schur {α β : Type*} (A : Finset α) (B : Finset β)
    (G : α → β → Prop) [DecidableRel G] (u : α → ℝ) (v : β → ℝ) (d : ℝ)
    (hrow : ∀ a ∈ A, ((B.filter (G a)).card : ℝ) ≤ d)
    (hcol : ∀ b ∈ B, ((A.filter (fun a => G a b)).card : ℝ) ≤ d) :
    (∑ a ∈ A, ∑ b ∈ B, if G a b then u a*v b else 0) ≤
      d/2*((∑ a ∈ A, u a^2)+(∑ b ∈ B, v b^2)) := by
  have hp (a : α) (b : β) : 2*(if G a b then u a*v b else 0) ≤
      (if G a b then u a^2 else 0)+(if G a b then v b^2 else 0) := by
    split_ifs
    · nlinarith [sq_nonneg (u a-v b)]
    · norm_num
  have hs := Finset.sum_le_sum (s := A) (fun a _ =>
    Finset.sum_le_sum (s := B) (fun b _ => hp a b))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hR : (∑ a ∈ A, ∑ b ∈ B, if G a b then u a^2 else 0) ≤ d*(∑ a ∈ A, u a^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hrow a ha) (sq_nonneg _)
  have hC : (∑ a ∈ A, ∑ b ∈ B, if G a b then v b^2 else 0) ≤ d*(∑ b ∈ B, v b^2) := by
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcol b hb) (sq_nonneg _)
  nlinarith

lemma graph_discarded_sumND {ι : Type*} (S : Finset ι) (G : ι → Prop)
    [DecidablePred G] (K : ι → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hK : ∀ i ∈ S, ¬G i → ‖K i‖ ≤ ε) :
    ‖(∑ i ∈ S, K i)-(∑ i ∈ S.filter G, K i)‖ ≤ S.card*ε := by
  classical
  have he : (∑ i ∈ S, K i)-(∑ i ∈ S.filter G, K i) =
      ∑ i ∈ S.filter (fun i => ¬G i), K i := by
    have h := Finset.sum_filter_add_sum_filter_not S G K
    linear_combination -h
  rw [he]
  calc
    _ ≤ ∑ i ∈ S.filter (fun i => ¬G i), ‖K i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S.filter (fun i => ¬G i), ε := Finset.sum_le_sum
      (fun i hi => hK i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
    _ ≤ S.card*ε := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le S _) hε

lemma graph_complex_schurND {α β : Type*} (A : Finset α) (B : Finset β)
    (G : α → β → Prop) [DecidableRel G] (F : α → ℂ) (H : β → ℂ) (D : ℝ)
    (hrow : ∀ a ∈ A, ((B.filter (G a)).card : ℝ) ≤ D)
    (hcol : ∀ b ∈ B, ((A.filter (fun a => G a b)).card : ℝ) ≤ D) :
    ‖∑ a ∈ A, ∑ b ∈ B, if G a b then F a*conj (H b) else 0‖ ≤
      D/2*((∑ a ∈ A, ‖F a‖^2)+(∑ b ∈ B, ‖H b‖^2)) := by
  calc
    _ ≤ ∑ a ∈ A, ∑ b ∈ B, if G a b then ‖F a‖*‖H b‖ else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      split_ifs <;> simp
    _ ≤ _ := finset_bipartite_schur A B G (fun a => ‖F a‖) (fun b => ‖H b‖) D hrow hcol

lemma graph_partition_schurND {α β κ : Type*} (A : Finset α) (B : Finset β)
    (C : Finset κ) (G : κ → α → β → Prop) [∀ k, DecidableRel (G k)]
    (F : α → ℂ) (H : β → ℂ) (η : κ → ℝ)
    (hη : ∀ k ∈ C, 0 ≤ η k) (hpart : ∑ k ∈ C, η k=1) (D : ℝ)
    (hrow : ∀ k ∈ C, ∀ a ∈ A, ((B.filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ C, ∀ b ∈ B, ((A.filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∑ k ∈ C, (η k:ℂ)*(∑ a ∈ A, ∑ b ∈ B, if G k a b then F a*conj (H b) else 0)‖ ≤
      D/2*((∑ a ∈ A, ‖F a‖^2)+(∑ b ∈ B, ‖H b‖^2)) := by
  calc
    _ ≤ ∑ k ∈ C, η k*(D/2*((∑ a ∈ A, ‖F a‖^2)+(∑ b ∈ B, ‖H b‖^2))) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hη k hk)]
      exact mul_le_mul_of_nonneg_left (graph_complex_schurND A B (G k) F H D
        (hrow k hk) (hcol k hk)) (hη k hk)
    _ = _ := by rw [← Finset.sum_mul,hpart,one_mul]

lemma graph_product_square_sumND {α β : Type*} (A : Finset α) (B : Finset β)
    (U : α → ℂ) (V : β → ℂ) :
    (∑ z ∈ A.product B, ‖U z.1*V z.2‖^2) =
      (∑ a ∈ A, ‖U a‖^2)*(∑ b ∈ B, ‖V b‖^2) := by
  rw [Finset.product_eq_sprod,Finset.sum_product]
  simp_rw [norm_mul,mul_pow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

lemma graph_partition_product_schurND {α β κ : Type*} (A : Finset α) (B : Finset β)
    (C : Finset κ) (G : κ → (α × β) → (α × β) → Prop) [∀ k, DecidableRel (G k)]
    (U₁ U₂ : α → ℂ) (V₁ V₂ : β → ℂ) (η : κ → ℝ)
    (hη : ∀ k ∈ C, 0 ≤ η k) (hpart : ∑ k ∈ C, η k=1) (D : ℝ)
    (hrow : ∀ k ∈ C, ∀ a ∈ A.product B, (((A.product B).filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ C, ∀ b ∈ A.product B, (((A.product B).filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∑ k ∈ C, (η k:ℂ)*(∑ a ∈ A.product B, ∑ b ∈ A.product B,
      if G k a b then (U₁ a.1*V₁ a.2)*conj (U₂ b.1*V₂ b.2) else 0)‖ ≤
      D/2*((∑ a ∈ A, ‖U₁ a‖^2)*(∑ b ∈ B, ‖V₁ b‖^2)+
        (∑ a ∈ A, ‖U₂ a‖^2)*(∑ b ∈ B, ‖V₂ b‖^2)) := by
  simpa only [graph_product_square_sumND] using graph_partition_schurND
    (A.product B) (A.product B) C G (fun z => U₁ z.1*V₁ z.2) (fun z => U₂ z.1*V₂ z.2)
    η hη hpart D hrow hcol

lemma graph_pair_partitionND {κ : Type*} (C : Finset κ) (η₁ η₂ : κ → ℝ)
    (h₁ : ∑ k ∈ C, η₁ k=1) (h₂ : ∑ k ∈ C, η₂ k=1) :
    ∑ k ∈ C.product C, η₁ k.1*η₂ k.2=1 := by
  rw [Finset.product_eq_sprod,Finset.sum_product,← Finset.sum_mul_sum,h₁,h₂,one_mul]

end Attempt4Near
end
end

end OAI
