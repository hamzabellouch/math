import Mathlib
import OAI.Analysis.VlasovMaxwell.Continuation.PhysicalBinBasePrefix

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma Admissible.uniform_particle_density_constant {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (t : ℝ), t ∈ Icc 0 T → ∀ (z : Phase), 0 ≤ s.f (t,z) ∧ s.f (t,z) ≤ C := by
  obtain ⟨C,hC⟩ := hd.1.continuous.bounded_above_of_compact_support hd.2.1
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro s T F hs h0 t ht z
  refine ⟨hs.nonnegative t ht z,?_⟩
  rw [F.transport_inverse hs.f_smooth hs.vlasov ht,h0]
  exact (le_abs_self _).trans ((hC _).trans (le_max_right _ _))

lemma Admissible.uniform_physicalBinDensity_constant {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (X V : ℝ→Vec) (B : ClosedConeBin) (t r : ℝ) (n : Sphere) (P θ σ : ℝ),
      r∈Icc 0 T → 0≤P → 0≤θ → 0≤σ → B.qmax≤P → B.dmax≤8*θ^2 → B.emax≤8*σ^2 →
      physicalBinDensity s X V B t r n≤ENNReal.ofReal (128*C*P^3*(min θ σ)^2) := by
  obtain ⟨C,hC,hb⟩ := Admissible.uniform_particle_density_constant hd
  refine ⟨C,hC,?_⟩
  intro s T F hs h0 X V B t r n P θ σ hr hP hθ hσ hq hd he
  exact coneBin_density_bound (sphere_norm n).le (norm_velocity_lt_one _).le hP hθ hσ hC
    hq hd he (fun v=>(hb s T F hs h0 r hr _).2)

lemma Admissible.uniform_actual_bin_Cauchy {d : Datum} (hd₀ : Admissible d) :
    ∃ C₀ : ℝ, 0≤C₀ ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀ z,s.f (0,z)=d.f₀ z) → ∀ (zX : Phase) (C : ClosedConeBin) (S : Set Phase)
      (a b I P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z => s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
      0<I → 0<P → 0≤θ → 0≤φ → 0≤σ → 0<C.rmin → 0<C.Dmin →
      C.qmax≤P → C.dmax≤8*θ^2 → C.Dmax≤8*φ^2 → C.emax≤8*σ^2 →
      (∀ D∈Icc C.Dmin C.Dmax, DyadicWindow k j (Real.sqrt (D/2))) →
      let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
      let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
      let N : ConeCoordinate → ℝ≥0∞ := fun z => physicalBinDensity s X V C z.1 z.2.1 z.2.2
      let D := ENNReal.ofReal (128*C₀*P^3*(min θ σ)^2)
      let M := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T C S a b (max 0 (a-C.rmax)) (min T (b-C.rmin))) /
          ENNReal.ofReal (C.rmin^2*C.Dmin)
      (∫⁻ z : ConeCoordinate, ENNReal.ofReal (z.1-z.2.1) *
        ENNReal.ofReal (prefixConeGood s T X z) * N z ∂physicalBinMeasure V C (Icc a b)) ≤
      (ENNReal.ofReal I * goodFieldBudget s X (fun t => velocity (V t)) k a b I j)^(1/2:ℝ) *
        (min (D^2*(volume (Icc a b)*ENNReal.ofReal (C.rmax-C.rmin)*ENNReal.ofReal (384*φ^2)))
          (D*M))^(1/2:ℝ) := by
  obtain ⟨C₀,hC₀,hbound⟩ := hd₀.uniform_physicalBinDensity_constant
  refine ⟨C₀,hC₀,?_⟩
  intro s T F hs hT h0 zX C S a b I P θ φ σ k j hS hS0 hJ hI hP hθ hφ hσ hR hD hq hd hDmax he hangle
  dsimp only
  let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
  let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
  let N : ConeCoordinate → ℝ≥0∞ := fun z => physicalBinDensity s X V C z.1 z.2.1 z.2.2
  let μ := physicalBinMeasure V C (Icc a b)
  have hα : Continuous (fun t => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  have hN : AEMeasurable N μ :=
    physicalBinDensity_aemeasurable hs hT hX hV C measurableSet_Icc hJ
  have hG := hs.measurable_prefixConeGood hT hX
  have hW : AEMeasurable (fun z : ConeCoordinate => ENNReal.ofReal (z.1-z.2.1)*
      ENNReal.ofReal (prefixConeGood s T X z)) μ :=
    ((measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal.mul hG.ennreal_ofReal).aemeasurable
  apply lintegral_product_bound_two μ hW hN
  · have hfield := hs.physicalBin_goodField hT hX hV C k j hJ hI hangle
    apply le_trans _ hfield
    apply le_of_eq
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
    have hg : 0≤prefixConeGood s T X z := add_nonneg (norm_nonneg _) (abs_nonneg _)
    dsimp only
    rw [mul_pow,← ENNReal.ofReal_pow hr,← ENNReal.ofReal_pow hg,← ENNReal.ofReal_mul (sq_nonneg _)]
  · apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    exact hbound s T F hs h0 X V C z.1 z.2.1 z.2.2 P θ σ
      ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩ hP.le hθ hσ hq hd he
  · have hmass := F.physicalBin_weighted_occupation hs hT zX C hS hS0 hJ hR.le hD.le
    have hμ : physicalBinMeasure (fun t => (F.flow zX t).2) C (Icc a b) = μ := by
      unfold μ physicalBinMeasure V
      rw [physicalBinBase_prefix zX C hJ]
    rw [hμ] at hmass
    have hne : ENNReal.ofReal (C.rmin^2*C.Dmin)≠0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)).mpr
    rw [mul_comm]
    convert hmass using 1
    congr 1
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    simp only [N,X,V,physicalBinDensity,prefixFlow,prefixClamp_eq (hJ hz.1)]
  · exact physicalBinMeasure_volume hV C measurableSet_Icc hφ hDmax

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma exists_direction_step {g : ℝ→Vec} {a b δ : ℝ} (hab : a≤b)
    (hg : ContinuousOn g (Icc a b)) (hδ : 0<δ) :
    ∃c∈Icc a b, (∀t∈Icc a c,‖g t-g a‖≤δ) ∧
      (c=b ∨ ‖g c-g a‖=δ) ∧ (a<b→a<c) := by
  classical
  let f := fun t=>‖g t-g a‖
  have hf : ContinuousOn f (Icc a b) := (hg.sub continuousOn_const).norm
  have hfa : f a=0 := by simp [f]
  by_cases hex : ∃t∈Icc a b,f t=δ
  · let S : Set ℝ := Icc a b ∩ f ⁻¹' {δ}
    have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
    obtain ⟨c,hc,hmin⟩ := hS.exists_isMinOn (by simpa only [S,Set.Nonempty,mem_inter_iff,
      mem_preimage,mem_singleton_iff] using hex) continuousOn_id
    have hfc : f c=δ := hc.2
    refine ⟨c,hc.1,?_,Or.inr hfc,?_⟩
    · intro t ht
      by_contra h
      have hft : δ<f t := lt_of_not_ge h
      obtain ⟨u,hu,he⟩ := intermediate_value_Icc ht.1
        (hf.mono (Icc_subset_Icc_right (ht.2.trans hc.1.2))) ⟨by simpa only [hfa] using hδ.le,hft.le⟩
      have huS : u∈S := ⟨⟨hu.1,hu.2.trans (ht.2.trans hc.1.2)⟩,he⟩
      have hct : c≤t := (hmin huS).trans hu.2
      have htc : t=c := le_antisymm ht.2 hct
      rw [htc,hfc] at hft
      exact (lt_irrefl δ hft)
    · intro _
      apply lt_of_le_of_ne hc.1.1
      intro he
      rw [←he,hfa] at hfc
      linarith
  · refine ⟨b,right_mem_Icc.mpr hab,?_,Or.inl rfl,fun h=>h⟩
    intro t ht
    by_contra h
    have hft : δ<f t := lt_of_not_ge h
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc ht.1
      (hf.mono (Icc_subset_Icc_right ht.2)) ⟨by simpa only [hfa] using hδ.le,hft.le⟩
    exact hex ⟨u,⟨hu.1,hu.2.trans ht.2⟩,he⟩

lemma exists_finite_direction_stops {g : ℝ→Vec} {a b δ ℓ : ℝ}
    (hab : a≤b) (hg : ContinuousOn g (Icc a b)) (hδ : 0<δ) (hℓ : 0<ℓ)
    (hmod : ∀s∈Icc a b,∀t∈Icc a b,|t-s|<ℓ→‖g t-g s‖<δ) :
    ∃n : ℕ,∃t : ℕ→ℝ,t 0=a ∧ t n=b ∧
      (∀i≤n,t i∈Icc a b) ∧
      (∀i<n,t i<t (i+1) ∧
        (∀x∈Icc (t i) (t (i+1)),‖g x-g (t i)‖≤δ) ∧
        (i+1<n→‖g (t (i+1))-g (t i)‖=δ ∧ ℓ≤t (i+1)-t i)) := by
  classical
  let S := Icc a b
  have hs : ∀x : S,∃c∈Icc x.1 b,(∀u∈Icc x.1 c,‖g u-g x.1‖≤δ) ∧
      (c=b ∨ ‖g c-g x.1‖=δ) ∧ (x.1<b→x.1<c) := fun x=>
    exists_direction_step x.2.2 (hg.mono (Icc_subset_Icc_left x.2.1)) hδ
  let next : S→S := fun x=>⟨(hs x).choose,⟨x.2.1.trans (hs x).choose_spec.1.1,
    (hs x).choose_spec.1.2⟩⟩
  let seq : ℕ→S := fun n=>(next^[n]) ⟨a,left_mem_Icc.mpr hab⟩
  let t : ℕ→ℝ := fun n=>(seq n).1
  have ht0 : t 0=a := rfl
  have hnext (i : ℕ) : seq (i+1)=next (seq i) := by
    exact Function.iterate_succ_apply' next i _
  have htmem (i : ℕ) : t i∈Icc a b := (seq i).2
  have hstep (i : ℕ) : t i≤t (i+1) ∧
      (∀u∈Icc (t i) (t (i+1)),‖g u-g (t i)‖≤δ) ∧
      (t (i+1)=b ∨ ‖g (t (i+1))-g (t i)‖=δ) ∧
      (t i<b→t i<t (i+1)) := by
    have hh := (hs (seq i)).choose_spec
    dsimp only [t]
    rw [hnext]
    exact ⟨hh.1.1,hh.2⟩
  have hm : Monotone t := monotone_nat_of_le_succ (fun i=>(hstep i).1)
  have hsep (i : ℕ) (hi : t (i+1)≠b) : ℓ≤t (i+1)-t i := by
    have he : ‖g (t (i+1))-g (t i)‖=δ := (hstep i).2.2.1.resolve_left hi
    by_contra hh
    have hl : |t (i+1)-t i|<ℓ := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hstep i).1)]
      exact lt_of_not_ge hh
    have hb := hmod (t i) (htmem i) (t (i+1)) (htmem (i+1)) hl
    rw [he] at hb
    exact lt_irrefl δ hb
  have hex : ∃n,t n=b := by
    by_contra hn
    have hne : ∀n,t n≠b := by simpa only [not_exists] using hn
    have hlower : ∀n : ℕ,a+(n:ℝ)*ℓ≤t n := by
      intro n
      induction n with
      | zero => simp only [Nat.cast_zero,zero_mul,add_zero,ht0,le_refl]
      | succ n ih =>
        have hh := hsep n (hne (n+1))
        rw [Nat.cast_add,Nat.cast_one]
        nlinarith
    obtain ⟨N,hN⟩ := exists_nat_gt ((b-a)/ℓ)
    have hh := (div_lt_iff₀ hℓ).mp hN
    have hNlo := hlower N
    have hNhi := (htmem N).2
    nlinarith
  let n := Nat.find hex
  have hnb : t n=b := Nat.find_spec hex
  have hnot : ∀i<n,t i≠b := fun i hi=>Nat.find_min hex hi
  refine ⟨n,t,ht0,hnb,fun i _=>htmem i,?_⟩
  intro i hi
  have hib : t i<b := lt_of_le_of_ne (htmem i).2 (hnot i hi)
  refine ⟨(hstep i).2.2.2 hib,(hstep i).2.1,?_⟩
  intro his
  exact ⟨(hstep i).2.2.1.resolve_left (hnot (i+1) his),hsep i (hnot (i+1) his)⟩

end RVM

end

end OAI
