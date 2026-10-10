import OAI.Probability.InvariantIsing.Cavity.OffsetFieldPopulation
import OAI.Probability.InvariantIsing.Fields.PhysicalFieldPopulationLimit
import OAI.Probability.InvariantIsing.Cavity.CavityPrefixAffineFamily

namespace OAI

/-! An affine block template and any physical model with the same limiting
finite populations have asymptotically identical mean pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem affine_template_pressure_comparison {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (q : ℕ) (hq : 0<q) (spec c : Fin m → ℕ) (hspec : ∑ a, spec a=n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0<ρ a) (hcount : ∀ a, (spec a : ℝ)=n*ρ a)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : (M : ℕ) → Fin M → A) (γ b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    (group : Fin n → A) (hgroup : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    {K B : ℝ} (hK : 0≤K) (hlam : ∀ a, |lam a|≤K) (hB : 0≤B) (hb : ∀ a, |b a|≤B) :
    let N := fun j => (∑ a, c a)+(q+j)*n
    Tendsto (fun j => (∫ U, rotatedPressure (fun i => lam (e (N j) i)) (matrixRotation U⁻¹)
      (fun i => b (g (N j) i)) ∂μ (N j))-
      ∫ U, rotatedPressure (fun i => lam (cavityAffineLabel hm spec c hspec (N j) i))
        (matrixRotation U⁻¹) (offsetBlockField (∑ a, c a) (q+j) (fun i => b (group i))) ∂μ (N j))
      atTop (𝓝 0) := by
  intro N
  have hN j : 0<N j := Nat.add_pos_right _ (Nat.mul_pos (by omega) hn)
  have hNl : Tendsto N atTop atTop := tendsto_atTop_mono (fun _ => Nat.le_add_left _ _)
    (by simpa only [Nat.add_comm] using cavityRationalDimension_tendsto n q hn)
  let f := fun j => cavityAffineLabel hm spec c hspec (N j)
  have hfcard j a : spinGroupSize (f j) a=cavityAffineCount spec c q j a := by
    dsimp only [f,N]
    rw [show (∑ a, c a)+(q+j)*n=cavityPrefixAffineSize n q c j by
      simp only [cavityPrefixAffineSize,Nat.add_comm]]
    rw [cavityPrefixAffineLabel_progression hm spec c hspec hn]
    exact cavityOrderedGroup_card _ _ a
  have hf : Tendsto (fun j a => (spinGroupSize (f j) a : ℝ)/N j) atTop (𝓝 ρ) := by
    apply tendsto_pi_nhds.mpr
    intro a
    have hratio : (spec a : ℝ)/n=ρ a := by
      rw [hcount, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
    simpa only [hfcard,N,cavityAffineSize,Nat.add_comm,hratio] using
      cavityAffineCount_ratio spec c hn hq a
  let gamma : Option A → ℝ := fun a => Option.elim a 0 γ
  let field : Option A → ℝ := fun a => Option.elim a 0 b
  have hfield a : |field a|≤B := by
    cases a with
    | none => simpa only [field,Option.elim_none,abs_zero] using hB
    | some a => exact hb a
  have hpop := offsetSiteGroup_population_tendsto hn (∑ a, c a) q hq group γ hgroup
  have htarget := someSiteGroup_population_tendsto N (fun j => g (N j)) γ (hg.comp hNl)
  have hh := physical_mean_joint_populations_tendsto N hN (fun j => μ (N j))
    f (fun j => e (N j)) ρ hρ hf (he.comp hNl) lam hK hlam
    (fun j => offsetSiteGroup (∑ a, c a) (q+j) group)
    (fun j i => some (g (N j) i)) gamma field
    (by simpa only [N,gamma,Nat.cast_add,Nat.cast_mul] using hpop) htarget hB hfield
  have hfield_eq j : (fun i => field (offsetSiteGroup (∑ a, c a) (q+j) group i))=
      offsetBlockField (∑ a, c a) (q+j) (fun i => b (group i)) :=
    offsetSiteGroup_field group b
  convert hh using 1
  funext j
  congr 1
  exact congrArg (fun z => ∫ U, rotatedPressure (fun i => lam (f j i))
    (matrixRotation U⁻¹) z ∂μ (N j)) (hfield_eq j).symm

end InvariantIsing

end

end OAI
