import Mathlib
import OAI.Probability.Ballisticity.Walk.Kernel

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

lemma sampled_kernel_sections {D E J W : Type*}
    [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace J] [MeasurableSpace W]
    [Countable J] [MeasurableSingletonClass J]
    (δ : Measure D) (σ : Measure E) (P : Measure W)
    [IsProbabilityMeasure δ] [IsProbabilityMeasure σ] [IsProbabilityMeasure P]
    (κ : Kernel D J) (s : D → E → J)
    (hs : Measurable (Function.uncurry s)) (hmap : ∀ d, σ.map (s d) = κ d)
    {f : D × W → ℝ} (hf : Measurable f) {Z : J → W → ℝ}
    (hZ : ∀ a, Measurable (Z a))
    (hi : Integrable (fun x : (D × E) × W => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2)
      ((δ.prod σ).prod P)) :
    ∀ᵐ x ∂δ.prod P, f x ≠ 0 → Integrable (fun a => Z a x.2) (κ x.1) := by
  have hz : Measurable (Function.uncurry Z) := measurable_from_prod_countable_right hZ
  let G : (D × E) × W → ℝ := fun x => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2
  have hG : Measurable G :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hz.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  have hp := swap_seed_preserving δ σ P
  have hj : Integrable (fun x : (D × W) × E => f x.1 * Z (s x.1.1 x.2) x.1.2)
      ((δ.prod P).prod σ) := (hp.integrable_comp hG.aestronglyMeasurable).mpr hi
  filter_upwards [hj.prod_right_ae] with x hx
  intro hfx
  have hzx : Integrable (fun u => Z (s x.1 u) x.2) σ := by
    have hh := hx.const_mul (f x)⁻¹
    simpa only [←mul_assoc, inv_mul_cancel₀ hfx, one_mul] using hh
  rw [←hmap]
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (hs.comp measurable_prodMk_left).aemeasurable).mpr hzx

lemma kernel_density_sections {D I A J : Type*} [MeasurableSpace D] [MeasurableSpace A] [Encodable I]
    [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
    [Nonempty J] [StandardBorelSpace J]
    (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]
    {f : D × (I → A) → ℝ} {Z : J → (I → A) → ℝ}
    {c Q : ℝ} (hc : 0 < c)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ a, Measurable (Z a)) (hZ0 : ∀ a ω, 0 ≤ Z a ω)
    (he : ∀ a, Integrable (fun ω => Real.exp (c * Z a ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ a, (∫ ω, Real.exp (c * Z a ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    (κ : Kernel D J) [IsMarkovKernel κ] :
    ∀ᵐ x ∂δ.prod (Measure.infinitePi (fun _ : I => ν)),
      f x ≠ 0 → Integrable (fun a => Z a x.2) (κ x.1) := by
  obtain ⟨s,hs,hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  let σ : Measure unitInterval := volume
  let g : (D × unitInterval) × (I → A) → ℝ := fun x => f (x.1.1,x.2)
  have hg : Measurable g := hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨_,hgH,_⟩ := randomized_density δ σ ν hf hfi hH
  have hi := integrable_density_mul_of_entropy hc hg
    (measurable_countable_sample hZ hs) (fun x => hf0 _) (fun x => hZ0 _ _) hgH
    (sampled_exponential_integrable (δ.prod σ) ν hZ he heQ hs).1
  exact sampled_kernel_sections δ σ (Measure.infinitePi (fun _ : I => ν))
    κ s hs hmap hf hZ hi

end TailDecorrelation

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma cut_neighborhoods_escape {d : ℕ} (e : Direction d) (a : ℝ)
    (k : Fin d) (L U : ℕ → ℤ)
    (hL : Tendsto L atTop atBot) (hU : Tendsto U atTop atTop)
    (N : ℕ) (S : Set (Lattice d)) (hS : S.Finite) :
    ∀ᶠ r in atTop, ∀ p : Lattice d × Lattice d,
      p.1 k ≤ L r → U r ≤ p.2 k → Disjoint S (upperPairNeighborhood e a p N) := by
  have hz : ∀ z ∈ S, ∀ᶠ r in atTop, ∀ p : Lattice d × Lattice d,
      p.1 k ≤ L r → U r ≤ p.2 k → z ∉ LatticeBall p.1 N ∪ LatticeBall p.2 N := by
    intro z _
    filter_upwards [(tendsto_atBot.mp hL) (z k - (N : ℤ) - 1),
      (tendsto_atTop.mp hU) (z k + (N : ℤ) + 1)] with r hrx hry
    intro p hp hq hz
    rcases hz with hz | hz
    · have hh := (abs_le.mp (hz k)).2
      omega
    · have hh := (abs_le.mp (hz k)).1
      omega
  filter_upwards [hS.eventually_all.mpr hz] with r hr
  intro p hp hq
  exact Set.disjoint_left.mpr fun z hz hz' => hr z hz p hp hq hz'.1

theorem actual_kernel_tail_decorrelation {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 0 < A ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice d × Lattice d,
        dot (realPosition x.1) (realPosition (step e)) =
          dot (realPosition x.2) (realPosition (step e)) →
        ∀ t : ℕ, 0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤
            2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e f A x ω) ∧
      let J := {p : Lattice d × Lattice d // p ∈ PairAtHeight (realPosition (step e)) 0}
      let Z : J → Environment d → ℝ := fun p => outwardCanonicalExcess e f A p.1
      BddAbove (Set.range (fun p => ∫ ω, Z p ω ∂environmentLaw ν)) ∧
      ∀ (D : Type) [MeasurableSpace D] (δ : Measure D) [IsProbabilityMeasure δ]
        (g : D × Environment d → ℝ),
        Measurable g → (∀ x, 0 ≤ g x) → Integrable g (δ.prod (environmentLaw ν)) →
        (∫ x, g x ∂δ.prod (environmentLaw ν)) = 1 →
        Integrable (fun x => TailDecorrelation.entropyPlus (g x)) (δ.prod (environmentLaw ν)) →
        ∀ (κ : ℕ → Kernel D J) [∀ r, IsMarkovKernel (κ r)] (L U : ℕ → D → ℤ),
          (∀ᵐ z ∂δ, Tendsto (fun r => L r z) atTop atBot ∧ Tendsto (fun r => U r z) atTop atTop) →
          (∀ r, ∀ᵐ z ∂δ, ∀ᵐ p ∂κ r z, p.1.1 f.1 ≤ L r z ∧ U r z ≤ p.1.2 f.1) →
          (∀ r, ∀ᵐ z ∂δ.prod (environmentLaw ν), g z ≠ 0 →
            Integrable (fun p => Z p z.2) (κ r z.1)) ∧
          (∀ r, Integrable (fun z => g z * (∫ p, Z p z.2 ∂κ r z.1)) (δ.prod (environmentLaw ν))) ∧
          (∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop,
            (∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1) ∂δ.prod (environmentLaw ν)) ≤
              (⨆ p, ∫ ω, Z p ω ∂environmentLaw ν) + ε) ∧
          Filter.limsup (fun r => ∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1)
            ∂δ.prod (environmentLaw ν)) atTop ≤ ⨆ p, ∫ ω, Z p ω ∂environmentLaw ν := by
  classical
  obtain ⟨A,c,B,hA,hc,hB,hbound,hloc⟩ := actual_outward_order ν hue e f hef htrans
  let J := {p : Lattice d × Lattice d // p ∈ PairAtHeight (realPosition (step e)) 0}
  let Z : J → Environment d → ℝ := fun p => outwardCanonicalExcess e f A p.1
  have hZm : ∀ p : J, Measurable (Z p) := fun p =>
    ((hbound 0 p.1 p.2).2.1).mono (rowSigma_le _) le_rfl
  have hZ0 : ∀ p : J, ∀ ω, 0 ≤ Z p ω := fun p => (hbound 0 p.1 p.2).1
  have he : ∀ p : J, Integrable (fun ω => Real.exp (c * Z p ω)) (environmentLaw ν) :=
    fun p => (hbound 0 p.1 p.2).2.2.1
  have heB : ∀ p : J, (∫ ω, Real.exp (c * Z p ω) ∂environmentLaw ν) ≤ B :=
    fun p => (hbound 0 p.1 p.2).2.2.2.1
  have hZi : ∀ p : J, Integrable (Z p) (environmentLaw ν) := fun p =>
    (integrable_and_mean_le_of_exp (environmentLaw ν) hc (hZm p) (hZ0 p) (he p) (heB p)).1
  have hZB : ∀ p : J, (∫ ω, Z p ω ∂environmentLaw ν) ≤ B / c := fun p =>
    (integrable_and_mean_le_of_exp (environmentLaw ν) hc (hZm p) (hZ0 p) (he p) (heB p)).2
  have hba : BddAbove (Set.range (fun p : J => ∫ ω, Z p ω ∂environmentLaw ν)) :=
    ⟨B/c, by rintro _ ⟨p,rfl⟩; exact hZB p⟩
  let p0 : J := ⟨(0,0), by simp [PairAtHeight, dot, realPosition]⟩
  let : Nonempty J := ⟨p0⟩
  have hC : 0 ≤ ⨆ p : J, ∫ ω, Z p ω ∂environmentLaw ν :=
    (integral_nonneg fun ω => hZ0 p0 ω).trans (le_ciSup hba p0)
  refine ⟨A,hA,outward_order_countable_event ν e f A (fun a x hx => (hbound a x hx).2.2.2.2),hba,?_⟩
  intro D mD δ hδ g hgm hg0 hgi hg1 hgH κ hκ L U hcuts htail
  have hcap : ∀ K η : ℝ, 0 < K → 0 < η → ∃ N : ℕ,
      ∃ F : J → Environment d → ℝ,
      (∀ p, @Measurable _ _ (TailDecorrelation.rows (upperPairNeighborhood e 0 p.1 N)) _ (F p)) ∧
      (∀ p ω, 0 ≤ F p ω ∧ F p ω ≤ K) ∧
      (∀ p, (∫ ω, |min K (Z p ω) - F p ω| ∂environmentLaw ν) ≤ η) := by
    intro K η hK hη
    obtain ⟨N,hN⟩ := outward_cap_locality_L1 ν e f A hloc hK hη
    have hh : ∀ p : J, ∃ F : Environment d → ℝ,
        @Measurable _ _ (rowSigma (upperPairNeighborhood e 0 p.1 N)) _ F ∧
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ K) ∧
        (∫ ω, |min (Z p ω) K - F ω| ∂environmentLaw ν) < η :=
      fun p => hN 0 p.1 p.2
    choose F hFm hFb hFe using hh
    refine ⟨N,F,?_,hFb,?_⟩
    · intro p
      rw [analytic_rows_eq]
      exact hFm p
    · intro p
      simpa only [min_comm] using (hFe p).le
  have hesc : ∀ N (S : Set (Lattice d)), S.Finite → ∀ᵐ z ∂δ,
      ∀ᶠ r in atTop, ∀ᵐ p ∂κ r z, Disjoint S (upperPairNeighborhood e 0 p.1 N) := by
    intro N S hS
    filter_upwards [hcuts, ae_all_iff.mpr htail] with z hz ht
    filter_upwards [cut_neighborhoods_escape e 0 f.1 (fun r => L r z) (fun r => U r z)
      hz.1 hz.2 N S hS] with r hr
    filter_upwards [ht r] with p hp
    exact hr p.1 hp.1 hp.2
  have he' : ∀ p : J, Integrable (fun ω => Real.exp ((2*(c/2)) * Z p ω)) (environmentLaw ν) := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using he
  have heB' : ∀ p : J, (∫ ω, Real.exp ((2*(c/2)) * Z p ω) ∂environmentLaw ν) ≤ B := by
    simpa only [show 2*(c/2) = c by ring] using heB
  refine ⟨fun r => TailDecorrelation.kernel_density_sections δ ν hc hgm hg0 hgi hgH
    hZm hZ0 he heB (κ r), ?_⟩
  refine ⟨fun r => TailDecorrelation.kernel_density_integrable δ ν hc hgm hg0 hgi hgH
    hZm hZ0 he heB (κ r), ?_⟩
  have hE := TailDecorrelation.kernel_entropy_decorrelation δ ν (by linarith : 0 < c/2) hC
      hgm hg0 hgi hg1 hgH hZm hZ0 he' heB' hZi (fun p => le_ciSup hba p)
      (fun N p => upperPairNeighborhood e 0 p.1 N) κ hcap hesc
  exact ⟨hE, TailDecorrelation.limsup_le_of_nonneg_eventual
    (fun r => integral_nonneg fun z => mul_nonneg (hg0 z) (integral_nonneg fun p => hZ0 _ _)) hE⟩

end DirectionalTransience

end

end OAI
