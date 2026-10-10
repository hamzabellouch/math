import OAI.Dynamics.ThreeTorus.ControlledBlocks

namespace OAI

/-! Good-arc flattening, exact predicted whitening, unconditional one-stage construction, and stage states and successors. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma PassagePackets.amplitude_supported {ι : Type*} (F : PassagePackets ι) (i : ι) :
    support (F.A i) ⊆ ((fun x : ℝ => (x : UnitAddCircle)) '' Icc F.l F.u) ×ˢ univ := by
  intro ua hua
  let x := circleRep F.o ua.1
  have hx : x ∈ Ioc F.o (F.o+1) := ((AddCircle.measurableEquivIoc 1 F.o) ua.1).2
  have he : F.A i ua = F.A₀ i ua.2 x := by
    simpa only [x,coe_circleRep] using F.lift_matches i ua.2 x hx
  have hxs : x ∈ Icc F.l F.u := Ioc_subset_Icc_self (F.support_lift i ua.2 (by change F.A₀ i ua.2 x ≠ 0; rwa [← he]))
  exact ⟨⟨x,hxs,coe_circleRep _ _⟩,mem_univ _⟩

/-- A literal spare-independent flat pair supported in the SAME good arc,
whose angular modes avoid the entire finite old family. -/
theorem PassagePackets.exists_disjoint_flat {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {δ : ℝ} (hδ : 0 < δ) (hg : F.GoodArc δ) :
    ∃ l u : ℝ, δ < l ∧ l < u ∧ u < 1-δ ∧
      (∀ i, support (F.A i) ⊆ ((fun x : ℝ => (x:UnitAddCircle)) '' Icc l u) ×ˢ univ) ∧
      ∃ k : ℤ, k ≠ 0 ∧ (∀ i, F.m i ≠ k ∧ F.m i ≠ -k) ∧
      ∃ A : UnitAddCircle × UnitAddCircle → ℂ,
        Measurable A ∧ MemLp A 2 slowVolume ∧ (∀ ua, conj (A ua) = A ua) ∧
        packetSpectralMeasure (fun z => (F.periodic.lift z:UnitAddCircle)) k A =
          ENNReal.ofReal (1/2:ℝ) • phaseHaar ∧
        packetSpectralMeasure (fun z => (F.periodic.lift z:UnitAddCircle)) (-k) A =
          ENNReal.ofReal (1/2:ℝ) • phaseHaar ∧
        support A ⊆ ((fun x : ℝ => (x:UnitAddCircle)) '' Icc l u) ×ˢ univ := by
  classical
  let l := (δ+F.l)/2
  let u := (F.u+1-δ)/2
  have hδl : δ < l := by dsimp [l]; linarith [hg.2.1]
  have hll : l < F.l := by dsimp [l]; linarith [hg.2.1]
  have huu : F.u < u := by dsimp [u]; linarith [hg.2.2.1]
  have huδ : u < 1-δ := by dsimp [u]; linarith [hg.2.2.1]
  have hlu : l < u := hll.trans_le (F.lu.trans huu.le)
  have hinc : Icc l u ⊆ Ioo δ (1-δ) := fun _ hx => ⟨hδl.trans_le hx.1,hx.2.trans_lt huδ⟩
  have he : (fun y : ℝ => F.periodic.lift (y:UnitAddCircle)) = F.V := by
    funext y
    exact F.periodic.lift_coe y
  have hD : ∀ x ∈ Icc l u, HasDerivWithinAt
      (fun y : ℝ => F.periodic.lift (y:UnitAddCircle)) (deriv F.V x) (Icc l u) x := by
    rw [he]
    intro x _
    exact (F.smooth_speed.differentiable (by simp)).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hmono : StrictMonoOn (fun y : ℝ => F.periodic.lift (y:UnitAddCircle)) (Icc l u) := by
    rw [he]
    exact strictMonoOn_of_deriv_pos (convex_Icc _ _) F.smooth_speed.continuous.continuousOn
      (fun x hx => hg.2.2.2 x (hinc (interior_subset hx)))
  let B := ∑ i, (F.m i).natAbs
  obtain ⟨k,hBk,hk,t,ht,hlt,hm,hLp,hr,hp,hn,hs⟩ := exists_flat_packet_spectra_above
    F.speed_continuous.measurable (F.smooth_speed.continuous_deriv (by simp)).measurable
    hlu hD hmono (o := 0) (fun x hx => ⟨by linarith [hinc hx |>.1],by linarith [hinc hx |>.2]⟩) B
  refine ⟨l,u,hδl,hlu,huδ,?_,(k:ℤ),by exact_mod_cast hk.ne',?_,_,hm,hLp,hr,hp,hn,?_⟩
  · intro i ua hua
    obtain ⟨⟨x,hx,hxe⟩,_⟩ := F.amplitude_supported i hua
    exact ⟨⟨x,⟨hll.le.trans hx.1,hx.2.trans huu.le⟩,hxe⟩,mem_univ _⟩
  · intro i
    have hi : (F.m i).natAbs ≤ B := Finset.single_le_sum (f := fun j => (F.m j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    constructor <;> intro hh <;> rw [hh] at hi <;> exact (not_le_of_gt hBk) (by simpa using hi)
  · intro ua hua
    obtain ⟨⟨x,hx,hxe⟩,_⟩ := hs hua
    exact ⟨⟨x,⟨hx.1,hx.2.trans ht.2⟩,hxe⟩,mem_univ _⟩

end ThreeTorus
end
end

section

/-! Whitening of the VERY SAME actual predicted output, retaining compact
support in its good arc, reality and literal Laurent approximation. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma paddedReflection_involutive {ι : Type*} {τ : ι → ι} (hτ : Involutive τ) :
    Involutive (Sum.map τ Bool.not) := by
  intro i
  cases i with
  | inl j => exact congrArg Sum.inl (hτ j)
  | inr b => cases b <;> rfl

namespace ColoredState
variable {n : ℕ} (C : ColoredState (Fin n))

lemma laurent_finite (c : ℤ →₀ ℂ) : C.laurent c = finitePacketLaurent
    (fun u => (C.packets.periodic.lift u:UnitAddCircle)) C.packets.m C.packets.A c := by
  funext x
  simp only [laurent,finitePacketLaurent,C.totalVector_eq,finitePacketVector]

/-- This theorem is unconditional once the concrete predicted smooth packet
family has been produced. The flat filler uses fresh actual angular modes. -/
theorem exists_whitening {τR : Fin n → Fin n} (hr : C.Reflection τR)
    (hτR : Involutive τR) {δ : ℝ} (hδ : 0 < δ) (hg : C.packets.GoodArc δ) :
    ∃ W : MeasurablePackets, ∃ l u : ℝ, δ < l ∧ l < u ∧ u < 1-δ ∧
      W.Supported l u ∧ (∃ τ, W.Reflection τ) ∧
      W.spectrum (fun z => (C.packets.periodic.lift z:UnitAddCircle)) = phaseHaar ∧
      (∫ x, ‖W.vector x-C.totalVector x‖^2 ∂tripleVolume) =
        (∫ z, blockTotal C.density z ∂phaseHaar)+1-
          2*(∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar) ∧
      ∀ (c : ℤ →₀ ℂ) (ε : ℝ), 0 < ε → ∃ d : ℤ →₀ ℂ,
        physicalError (C.laurent c) (finitePacketLaurent
          (fun z => (C.packets.periodic.lift z:UnitAddCircle)) W.m W.A d) < ε^2 := by
  classical
  let : MeasurableSpace C.Index := ⊤
  let : MeasurableSingletonClass C.Index := ⟨fun _ => trivial⟩
  let : MeasurableSingletonClass (C.Index ⊕ Bool) := by
    constructor
    intro i
    cases i with
    | inl j => simpa only [Set.image_singleton] using (measurableSet_singleton j).inl_image (β := Bool)
    | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image (α := C.Index)
  let φ : UnitAddCircle → UnitAddCircle := fun z => (C.packets.periodic.lift z:UnitAddCircle)
  have hφ : Measurable φ := AddCircle.measurable_mk'.comp C.packets.speed_continuous.measurable
  let p := blockTotal C.density
  have hp : Continuous p := continuous_finsetSum _ (fun r _ => C.density_continuous r)
  have hpn : ∀ z, 0 ≤ p z := fun z => Finset.sum_nonneg (fun r _ => C.density_nonneg r z)
  obtain ⟨l,u,hdl,hlu,hud,hAs,k,hk,havoid,V,hVm,hVlp,hVr,hVp,hVn,hVs⟩ :=
    C.packets.exists_disjoint_flat hδ hg
  let m := paddedAngular C.packets.m k
  let A := paddedOld C.packets.A
  let B := paddedFlat (ι := C.Index) V
  have hmi : Injective m := paddedAngular_injective C.injective hk havoid
  have hmn : ∀ i, m i ≠ 0 := by
    intro i
    cases i with
    | inl j => exact C.packets.nonzero j
    | inr b => cases b <;> simpa [m,paddedAngular] using hk
  have hAm : ∀ i, Measurable (A i) := by
    intro i
    cases i with
    | inl j => exact (C.packets.continuous_amplitude j).measurable
    | inr _ => exact measurable_const
  have hBm : ∀ i, Measurable (B i) := by
    intro i
    cases i with
    | inl _ => exact measurable_const
    | inr _ => exact hVm
  have hAlp : ∀ i, MemLp (A i) 2 slowVolume := by
    intro i
    cases i with
    | inl j => exact C.measurablePackets.memLp j
    | inr _ => exact MemLp.zero
  have hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)) := by
    rw [finitePacketSpectralMeasure_paddedOld hφ _ _ (fun i => (C.packets.continuous_amplitude i).measurable)]
    rw [finitePacketSpectralMeasure_eq_sum hφ _ (fun i => (C.packets.continuous_amplitude i).measurable)]
    exact C.measurablePackets_spectrum
  have hflat : finitePacketSpectralMeasure φ m B = phaseHaar :=
    finitePacketSpectralMeasure_paddedFlat hφ _ _ hVm hVp hVn
  let W : MeasurablePackets := {
    Index := C.Index ⊕ Bool
    finite := inferInstance
    m := m
    injective := hmi
    nonzero := hmn
    A := whitenPackets φ m p A B
    measurable := measurable_whitenPackets hφ m hp.measurable hAm hBm
    memLp := memLp_whitenPackets hφ m hp.measurable hpn hAm hBm hpush hflat }
  have heA : finitePacketVector m A = C.totalVector :=
    (finitePacketVector_paddedOld _ _ _).trans C.measurablePackets_vector
  have hW : finitePacketSpectralMeasure φ m W.A = phaseHaar :=
    whitenPackets_flat hφ m hp.measurable hpn hAm hBm hpush hflat
  refine ⟨W,l,u,hdl,hlu,hud,?_,?_,?_,?_,?_⟩
  · apply whitenPackets_support
    · intro i
      cases i with
      | inl j => exact hAs j
      | inr _ => simp [paddedOld]
    · intro i
      cases i with
      | inl _ => simp [paddedFlat]
      | inr _ => exact hVs
  · have heven := C.totalDensity_even hr hτR
    obtain ⟨τ,hτ,hcolor⟩ := hr
    have hτi := hτ.involutive C.injective
    refine ⟨Sum.map τ Bool.not,paddedReflection_involutive hτi,?_,?_⟩
    · intro i
      cases i with
      | inl j => exact hτ.index j
      | inr b => cases b <;> simp [W,m,paddedAngular]
    · apply whitenPackets_reflection
      · intro i
        cases i with
        | inl j => exact hτ.index j
        | inr b => cases b <;> simp [m,paddedAngular]
      · exact heven
      · intro i ua
        cases i with
        | inl j => exact hτ.amplitude j ua
        | inr _ => simp [paddedOld]
      · intro i ua
        cases i with
        | inl _ => simp [paddedFlat]
        | inr _ => exact (hVr ua).symm
  · exact (W.spectrum_eq hφ).trans hW
  · have he := whitenPackets_distance_mass hφ hmi hp hpn hAm hBm hAlp hpush hflat
    rw [heA,← C.total_mass_energy] at he
    exact he
  · intro c ε hε
    let D : UnitAddCircle → ℂ := fun z => ∑ k ∈ c.support, c k*fourier k z
    have hD : Continuous D := continuous_finsetSum _ (fun k _ => continuous_const.mul (fourier k).continuous)
    obtain ⟨d,hd⟩ := exists_whitened_laurent_approx hφ hmi hp hpn hAm hBm hpush hflat hD hε
    refine ⟨d,?_⟩
    have he : finitePacketVector m (multiplyPackets φ m D A) = C.laurent c := by
      funext x
      change finitePacketVector m (multiplyPackets φ m (fun z => ∑ k ∈ c.support, c k*fourier k z) A) x = _
      rw [← finitePacketLaurent_eq_multiplier]
      simp only [finitePacketLaurent,heA,laurent]
      rfl
    rw [he] at hd
    exact hd

end ColoredState
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma MeasurablePackets.laurent_memLp (W : MeasurablePackets)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) (c : ℤ →₀ ℂ) :
    MemLp (finitePacketLaurent φ W.m W.A c) 2 tripleVolume := by
  have he : finitePacketLaurent φ W.m W.A c = finitePacketVector W.m
      (multiplyPackets φ W.m (fun z => ∑ k ∈ c.support, c k*fourier k z) W.A) :=
    funext (finitePacketLaurent_eq_multiplier φ W.m W.A c)
  rw [he]
  apply memLp_finitePacketVector
  exact memLp_multiplyPackets hφ W.m (continuous_finsetSum _
    (fun k _ => continuous_const.mul (fourier k).continuous)) W.measurable W.memLp

lemma ColoredState.density_integrable {n : ℕ} (C : ColoredState (Fin n)) :
    Integrable (blockTotal C.density) phaseHaar :=
  integrable_finsetSum _ (fun i _ => (C.density_continuous i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

lemma ColoredState.mass_eq_norm_sq {n : ℕ} (C : ColoredState (Fin n)) :
    (∫ z, blockTotal C.density z ∂phaseHaar)=physicalDist C.totalVector 0^2 := by
  rw [physicalDist_sq,physicalError]
  simpa only [Pi.zero_apply,sub_zero] using C.total_mass_energy

/-- The ACTUAL reflected prediction output is whitened, not replaced by an
unrelated Hilbert witness. Small input density error controls the same vector. -/
theorem exists_predicted_whitening {n : ℕ} (C : ColoredState (Fin n))
    (ρ : Fin n → Fin n) (hρ : Involutive ρ) (hr : C.Reflection ρ)
    (b : Fin n → ℂ) (hb : ∀ i, b (ρ i)=conj (b i))
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {e r η κ ζ : ℝ} (he : 0 < e) (hr0 : 0 < r) (hr1 : r < 1)
    (her : e ≤ (r^2/64)^2) (hη : 0 < η) (hκ : 0 < κ) (hζ : 0 < ζ)
    (hpC : (∫ z, |blockTotal C.density z-1| ∂phaseHaar) < e) :
    ∃ W : MeasurablePackets, ∃ V : ℝ → ℝ, ∃ hp : Periodic V 1,
      ∃ _hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V,
      ∃ δ l u : ℝ, ∃ β : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame, ∃ d : ℤ →₀ ℂ,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ δ < l ∧ l < u ∧ u < 1-δ ∧
      (∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) ∧ W.Supported l u ∧
      (∃ τ, W.Reflection τ) ∧ W.spectrum (fun z => (hp.lift z:UnitAddCircle))=phaseHaar ∧
      Continuous β ∧ MeasurePreserving β tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans β ∧ Q.Close ζ frame C.packets.V frame' V ∧
      physicalDist C.totalVector (W.vector ∘ β) < e+r ∧
      physicalDist (fun x => ∑ i, b i*C.vector i x)
        (finitePacketLaurent (fun z => (hp.lift z:UnitAddCircle)) W.m W.A d ∘ β) < η := by
  classical
  let s := r^2/64
  have hs0 : 0 < s := div_pos (sq_pos_of_pos hr0) (by norm_num)
  have hs1 : s < 1 := by dsimp [s]; nlinarith
  have hes : e ≤ s := by change e ≤ s^2 at her; nlinarith
  have he1 : e < 1 := hes.trans_lt hs1
  have hsqrt : Real.sqrt e ≤ s := (Real.sqrt_le_iff).2 ⟨hs0.le,her⟩
  have hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 1+e := by
    have ht := norm_integral_le_integral_norm (fun z => blockTotal C.density z-1) (μ := phaseHaar)
    rw [integral_sub C.density_integrable (integrable_const _)] at ht
    simp only [integral_const,probReal_univ,smul_eq_mul,mul_one,Real.norm_eq_abs] at ht
    have hh := le_abs_self ((∫ z, blockTotal C.density z ∂phaseHaar)-1)
    linarith
  have hnC : physicalDist C.totalVector 0 < 1+e := by
    rw [C.mass_eq_norm_sq] at hmass
    nlinarith [physicalDist_nonneg C.totalVector 0]
  have hHellinger : 1-Real.sqrt e < ∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar := by
    have hh := density_hellinger_error C.density_integrable (integrable_const (1:ℝ))
      (Filter.Eventually.of_forall (fun z => Finset.sum_nonneg (fun i _ => C.density_nonneg i z)))
      (Filter.Eventually.of_forall (fun _ => zero_le_one))
    simp only [Real.sqrt_one,integral_const,probReal_univ,smul_eq_mul,mul_one] at hh
    have hh' := (neg_le_abs ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-1)).trans hh
    have he' := Real.sqrt_lt_sqrt (integral_nonneg fun z => abs_nonneg _) hpC
    linarith
  let t := e/((n:ℝ)+1)
  have ht : 0 < t := div_pos he (by positivity)
  let a := min (t^2) ζ
  have ha : 0 < a := lt_min (sq_pos_of_pos ht) hζ
  obtain ⟨E,β,c,K,A,hK,hpath,hphys,hHell,hpred,hEmass,hEr,⟨δ,hδ,hδ8,hδκ,hEg⟩,frame',hfr,hjet⟩ :=
    actual_controlled_tagged_prediction C ρ hρ hr b hb (half_pos hη) hs0 ha hκ
      (hmass.trans (by linarith)) Q frame
  have hCE : physicalDist C.totalVector (E.totalVector ∘ β) < e := by
    have hg i : physicalDist (C.vector i) (E.vector i ∘ β) ≤ t := by
      apply ((physicalDist_lt_iff _ _ ht).2 ?_).le
      exact (hphys i).trans_le (min_le_left _ _)
    have hh := finite_weighted_dist_le C.vector_continuous
      (fun i => (E.vector_continuous i).comp hpath.continuous) (fun _ => (1:ℂ)) hg
    simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
    refine hh.trans_lt ?_
    dsimp [t]
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < (n:ℝ)+1)).2
    nlinarith
  have hnE : physicalDist E.totalVector 0 < 1+2*e := by
    have hh := physicalDist_triangle (continuous_triple_memLp (E.totalVector_continuous.comp hpath.continuous))
      (continuous_triple_memLp C.totalVector_continuous) MemLp.zero
    rw [physicalDist_symm (E.totalVector ∘ β) C.totalVector] at hh
    have hz : (0 : TripleTorus → ℂ) ∘ β = 0 := rfl
    rw [← hz,physicalDist_continuous_comp β hpath.continuous hpath.preserves] at hh
    simp only [hz] at hh
    linarith
  obtain ⟨W,l,u,hdl,hlu,hud,hWs,hWr,hWflat,hWdist,hWrecon⟩ := E.exists_whitening hEr hρ hδ hEg
  have hWE : physicalDist W.vector E.totalVector < r := by
    apply (physicalDist_lt_iff _ _ hr0).2
    change physicalError W.vector E.totalVector = _ at hWdist
    rw [hWdist,E.mass_eq_norm_sq]
    have hnE0 := physicalDist_nonneg E.totalVector 0
    have he2 : e^2 ≤ e := by nlinarith
    have hnorm : physicalDist E.totalVector 0^2 < (1+2*e)^2 := by nlinarith
    have hHell' : 1-2*s < ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar := by linarith
    have hsdef : 64*s=r^2 := by dsimp [s]; ring
    nlinarith
  obtain ⟨d,hd⟩ := hWrecon c (η/2) (half_pos hη)
  let V := E.packets.V
  let hp := E.packets.periodic
  have hφ : Measurable (fun z => (hp.lift z:UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp E.packets.speed_continuous.measurable
  refine ⟨W,V,hp,E.packets.smooth_speed,δ,l,u,β,frame',d,hδ,hδ8,hδκ,hdl,hlu,hud,
    hEg.2.2.2,hWs,hWr,hWflat,hpath.continuous,hpath.preserves,hfr,hjet.mono (min_le_right _ _),?_,?_⟩
  · have hEW : physicalDist (E.totalVector ∘ β) (W.vector ∘ β) < r := by
      rw [physicalDist_continuous_comp β hpath.continuous hpath.preserves,physicalDist_symm]
      exact hWE
    exact (physicalDist_triangle (continuous_triple_memLp C.totalVector_continuous)
      (continuous_triple_memLp (E.totalVector_continuous.comp hpath.continuous))
      (W.vector_memLp.comp_measurePreserving hpath.preserves)).trans_lt (add_lt_add hCE hEW)
  · have htag : Continuous (fun x => ∑ i, b i*C.vector i x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (C.vector_continuous i))
    have hpr := (physicalDist_lt_iff _ _ (half_pos hη)).2 hpred
    have hrec : physicalDist (E.laurent c ∘ β)
        (finitePacketLaurent (fun z => (hp.lift z:UnitAddCircle)) W.m W.A d ∘ β) < η/2 := by
      rw [physicalDist_continuous_comp β hpath.continuous hpath.preserves]
      exact (physicalDist_lt_iff _ _ (half_pos hη)).2 hd
    exact (physicalDist_triangle (continuous_triple_memLp htag)
      (continuous_triple_memLp ((E.laurent_continuous c).comp hpath.continuous))
      ((W.laurent_memLp hφ d).comp_measurePreserving hpath.preserves)).trans_lt (by linarith)
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- The unconditional one-stage producer (source05 Proposition `stage`). All
packets, tags, two separations, actual prediction and whitening are constructed.
The three tolerances are independent; finite physical jets include both signs. -/
theorem exists_one_stage (F : MeasurablePackets)
    {τ : F.Index → F.Index} (hr : F.Reflection τ)
    {δ l u : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2) (hdl : δ < l) (hud : u < 1-δ)
    (hsupp : F.Supported l u)
    (V : ℝ → ℝ) (hp : Periodic V 1) (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hv : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x)
    (hflat : F.spectrum (fun z => (hp.lift z:UnitAddCircle))=phaseHaar)
    {h : TripleTorus → ℂ} (hh : Continuous h) (hrh : ∀ x, conj (h x)=h x)
    (hch : ∫ x, h x ∂tripleVolume=0) (hbh : ∀ x, ‖h x‖ ≤ 1)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε η κ ζ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ W : MeasurablePackets, ∃ V' : ℝ → ℝ, ∃ hp' : Periodic V' 1,
      ∃ _hs' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V',
      ∃ δ' l' u' : ℝ, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame, ∃ c : ℤ →₀ ℂ,
      0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ δ' < l' ∧ l' < u' ∧ u' < 1-δ' ∧
      (∀ x ∈ Ioo δ' (1-δ'), 0 < deriv V' x) ∧ W.Supported l' u' ∧
      (∃ τ', W.Reflection τ') ∧ W.spectrum (fun z => (hp'.lift z:UnitAddCircle))=phaseHaar ∧
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ Q.Close ζ frame V frame' V' ∧
      physicalDist F.vector (W.vector ∘ α) < ε ∧
      physicalDist h (finitePacketLaurent (fun z => (hp'.lift z:UnitAddCircle)) W.m W.A c ∘ α)
        < Real.sqrt (2*δ)+η := by
  let r := min (ε/8) (1/8)
  have hr0 : 0 < r := lt_min (by positivity) (by norm_num)
  have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hrε : 8*r ≤ ε := by have := min_le_left (ε/8) (1/8); dsimp [r]; linarith
  let e := min ((r^2/64)^2) (min (η/4) (r/4))
  have he : 0 < e := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have her : e ≤ (r^2/64)^2 := min_le_left _ _
  have heη : e ≤ η/4 := (min_le_right _ _).trans (min_le_left _ _)
  have her' : e ≤ r/4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n,C,ρ,b,α,P,hαc,hαm,hP,hρ,hCr,hb,hgood,hjet,hFC,hHC,hpC⟩ :=
    exists_prediction_ready F hr hδ hd hdl hud hsupp V hp hs hv hflat hh hrh hch hbh Q frame he hκ (half_pos hζ)
  obtain ⟨W,V',hp',hs',δ',l',u',β,P',c,hδ',hδ8,hδκ,hdl',hlu',hud',hv',hWs,hWr,hWflat,
    hβc,hβm,hP',hjet',hCW,hHW⟩ := exists_predicted_whitening C ρ hρ hCr b hb Q P he hr0 hr1 her
      (half_pos hη) hκ (half_pos hζ) hpC
  have hβαc : Continuous (α.trans β) := hβc.comp hαc
  have hβαm : MeasurePreserving (α.trans β) tripleVolume tripleVolume := hβm.comp hαm
  have hφ : Measurable (fun z => (hp'.lift z:UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (continuous_of_continuous_lift (by simpa only [Periodic.lift_coe] using hs'.continuous)).measurable
  refine ⟨W,V',hp',hs',δ',l',u',α.trans β,P',c,hδ',hδ8,hδκ,hdl',hlu',hud',hv',hWs,hWr,
    hWflat,hβαc,hβαm,?_,(hjet.trans hjet').mono (by linarith),?_,?_⟩
  · rw [hP',hP]; rfl
  · have ht := physicalDist_triangle F.vector_memLp
      (continuous_triple_memLp (C.totalVector_continuous.comp hαc))
      (W.vector_memLp.comp_measurePreserving hβαm)
    have hCW' : physicalDist (C.totalVector ∘ α) (W.vector ∘ (α.trans β)) < e+r := by
      change physicalDist (C.totalVector ∘ α) ((W.vector ∘ β) ∘ α) < e+r
      rw [physicalDist_continuous_comp α hαc hαm]
      exact hCW
    linarith
  · have hctag : Continuous (fun x => ∑ i, b i*C.vector i x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (C.vector_continuous i))
    have hHW' : physicalDist ((fun x => ∑ i, b i*C.vector i x) ∘ α)
        (finitePacketLaurent (fun z => (hp'.lift z:UnitAddCircle)) W.m W.A c ∘ (α.trans β)) < η/2 := by
      change physicalDist ((fun x => ∑ i, b i*C.vector i x) ∘ α)
        ((finitePacketLaurent (fun z => (hp'.lift z:UnitAddCircle)) W.m W.A c ∘ β) ∘ α) < η/2
      rw [physicalDist_continuous_comp α hαc hαm]
      exact hHW
    have ht := physicalDist_triangle (continuous_triple_memLp hh)
      (continuous_triple_memLp (hctag.comp hαc))
      ((W.laurent_memLp hφ c).comp_measurePreserving hβαm)
    linarith
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma measurePreserving_shear {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {f : X → UnitAddCircle} (hf : Measurable f) :
    MeasurePreserving (fun x : UnitAddCircle × X => (x.1+f x.2,x.2))
      (AddCircle.haarAddCircle.prod ν) (AddCircle.haarAddCircle.prod ν) := by
  have hh := (MeasurePreserving.id ν).skew_product (g := fun (x : X) (θ : UnitAddCircle) => θ+f x)
    (measurable_snd.add (hf.comp measurable_fst))
    (Filter.Eventually.of_forall (fun x => map_add_right_eq_self AddCircle.haarAddCircle (f x)))
  exact Measure.measurePreserving_swap.comp (hh.comp Measure.measurePreserving_swap)

/-- Literal admissible states in physical coordinates. No successor or basis is
part of the data; successors are produced by the unconditional stage theorem. -/
structure StageState where
  frame : PhysicalFrame
  chart_cont : Continuous frame.chart
  chart_mp : MeasurePreserving frame.chart tripleVolume tripleVolume
  packets : MeasurablePackets
  reflected : ∃ τ, packets.Reflection τ
  V : ℝ → ℝ
  periodic : Periodic V 1
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V
  δ : ℝ
  l : ℝ
  u : ℝ
  δ_pos : 0 < δ
  δ_half : δ < 1/2
  δ_l : δ < l
  l_u : l < u
  u_δ : u < 1-δ
  increasing : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x
  supported : packets.Supported l u
  flat : packets.spectrum (fun z => (periodic.lift z : UnitAddCircle)) = phaseHaar

namespace StageState
variable (s : StageState)
def speed (z : UnitAddCircle) : UnitAddCircle := (s.periodic.lift z : UnitAddCircle)
lemma speed_cont : Continuous s.speed :=
  (AddCircle.continuous_mk' 1).comp (continuous_of_continuous_lift
    (by simpa only [Periodic.lift_coe] using s.smooth.continuous))
def chartHomeo : TripleTorus ≃ₜ TripleTorus := s.chart_cont.homeoOfEquivCompactToT2
lemma chart_symm_cont : Continuous s.frame.chart.symm := s.chartHomeo.symm.continuous
lemma chart_symm_mp : MeasurePreserving s.frame.chart.symm tripleVolume tripleVolume :=
  MeasurePreserving.symm s.chartHomeo.toMeasurableEquiv s.chart_mp

def twistEquiv (φ : UnitAddCircle → UnitAddCircle) : Equiv.Perm TripleTorus where
  toFun x := (x.1+φ x.2.1,x.2)
  invFun x := (x.1-φ x.2.1,x.2)
  left_inv x := by simp
  right_inv x := by simp

def mapPow (k : ℤ) : Equiv.Perm TripleTorus :=
  s.frame.chart.trans ((twistEquiv (fun z => k • s.speed z)).trans s.frame.chart.symm)

def vector : TripleTorus → ℂ := s.packets.vector ∘ s.frame.chart
lemma vector_memLp : MemLp s.vector 2 tripleVolume :=
  s.packets.vector_memLp.comp_measurePreserving s.chart_mp
abbrev L2 := Lp ℂ 2 tripleVolume
def vec : L2 := s.vector_memLp.toLp s.vector
lemma vec_ae : s.vec =ᵐ[tripleVolume] s.vector := MemLp.coeFn_toLp _

lemma mapPow_cont (k : ℤ) : Continuous (s.mapPow k) := by
  change Continuous (fun x => s.frame.chart.symm
    ((s.frame.chart x).1 + k • s.speed (s.frame.chart x).2.1,
      (s.frame.chart x).2))
  exact s.chart_symm_cont.comp ((s.chart_cont.fst.add
    ((s.speed_cont.comp s.chart_cont.snd.fst).const_smul k)).prodMk s.chart_cont.snd)
lemma mapPow_mp (k : ℤ) : MeasurePreserving (s.mapPow k) tripleVolume tripleVolume :=
  s.chart_symm_mp.comp ((measurePreserving_shear ((s.speed_cont.measurable.const_smul k).comp measurable_fst)).comp s.chart_mp)

lemma mapPow_apply (k : ℤ) (x : TripleTorus) :
    s.mapPow k x = s.frame.chart.symm (twistIter s.speed k (s.frame.chart x)) := by
  rfl
lemma mapPow_add (k j : ℤ) (x : TripleTorus) :
    s.mapPow (k+j) x = s.mapPow k (s.mapPow j x) := by
  simp only [mapPow_apply,s.frame.chart.apply_symm_apply,twistIter_add]
lemma mapPow_zero (x : TripleTorus) : s.mapPow 0 x = x := by
  simp [mapPow_apply,twistIter]
lemma mapPow_graph (k : ℤ) (x : Cover) :
    tripleProject (s.frame.mapLift s.V k x) = s.mapPow k (tripleProject x) := by
  rw [PhysicalFrame.mapLift,Function.comp_apply,Function.comp_apply,s.frame.backward_graph]
  rw [mapPow_apply,← s.frame.forward_graph]
  congr 1
  change (((s.frame.forward x 0+(k:ℝ)*s.V (s.frame.forward x 1):ℝ):UnitAddCircle),
    (s.frame.forward x 1:UnitAddCircle),(s.frame.forward x 2:UnitAddCircle)) = _
  change (((s.frame.forward x 0+(k:ℝ)*s.V (s.frame.forward x 1):ℝ):UnitAddCircle),
    (s.frame.forward x 1:UnitAddCircle),(s.frame.forward x 2:UnitAddCircle)) =
    ((s.frame.forward x 0:UnitAddCircle)+k • (s.V (s.frame.forward x 1):UnitAddCircle),
      (s.frame.forward x 1:UnitAddCircle),(s.frame.forward x 2:UnitAddCircle))
  simp only [AddCircle.coe_add,← zsmul_eq_mul,AddCircle.coe_zsmul]

lemma vector_centered : ∫ x, s.vector x ∂tripleVolume = 0 := by
  simp only [vector,Function.comp_apply]
  rw [s.chart_mp.integral_comp s.chartHomeo.toMeasurableEquiv.measurableEmbedding]
  exact s.packets.vector_centered
lemma vector_real (x : TripleTorus) : conj (s.vector x)=s.vector x := by
  obtain ⟨τ,hτ⟩ := s.reflected
  exact s.packets.vector_real hτ _

def orbit (k : ℤ) : L2 := Lp.compMeasurePreserving (s.mapPow k) (s.mapPow_mp k) s.vec
lemma orbit_ae (k : ℤ) : s.orbit k =ᵐ[tripleVolume] fun x => s.vector (s.mapPow k x) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving s.vec (s.mapPow_mp k),
    (s.mapPow_mp k).quasiMeasurePreserving.ae s.vec_ae] with x hx hy
  exact hx.trans hy

def laurent (c : ℤ →₀ ℂ) : L2 := c.sum (fun k a => a • s.orbit k)
lemma laurent_ae (c : ℤ →₀ ℂ) : s.laurent c =ᵐ[tripleVolume]
    finitePacketLaurent s.speed s.packets.m s.packets.A c ∘ s.frame.chart := by
  classical
  have ha := ae_all_iff.mpr (fun k => s.orbit_ae k)
  filter_upwards [Lp.coeFn_finsetSum (c.support) (fun k => c k • s.orbit k),ha,
    ae_all_iff.mpr (fun k => Lp.coeFn_smul (c k) (s.orbit k))] with x hx hy hz
  change (∑ k ∈ c.support, c k • s.orbit k) x = _ at hx ⊢
  rw [hx]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hz,hy,vector,mapPow_apply,
    Function.comp_apply,s.frame.chart.apply_symm_apply,finitePacketLaurent,MeasurablePackets.vector]

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- A real bounded physical test. The dense test family will be constructed
explicitly; this structure only records the hypotheses of the one-stage lemma. -/
structure PhysicalTest where
  fn : C(TripleTorus,ℂ)
  real : ∀ x, conj (fn x)=fn x
  centered : ∫ x, fn x ∂tripleVolume=0
  bound : ∀ x, ‖fn x‖ ≤ 1
namespace PhysicalTest
variable (h : PhysicalTest)
lemma memLp : MemLp h.fn 2 tripleVolume := continuous_triple_memLp h.fn.continuous
def vec : StageState.L2 := h.memLp.toLp h.fn
lemma vec_ae : h.vec =ᵐ[tripleVolume] h.fn := MemLp.coeFn_toLp _
end PhysicalTest

lemma physicalDist_reps {f g : TripleTorus → ℂ} {F G : StageState.L2}
    (hf : F =ᵐ[tripleVolume] f) (hg : G =ᵐ[tripleVolume] g) :
    physicalDist f g = dist F G := by
  have hfl : MemLp f 2 tripleVolume := (Lp.memLp F).ae_eq hf
  have hgl : MemLp g 2 tripleVolume := (Lp.memLp G).ae_eq hg
  have hF : hfl.toLp f=F := Lp.ext (hfl.coeFn_toLp.trans hf.symm)
  have hG : hgl.toLp g=G := Lp.ext (hgl.coeFn_toLp.trans hg.symm)
  rw [physicalDist_eq_norm hfl hgl,hF,hG,dist_eq_norm]

namespace StageState
/-- The already proved stage producer, transferred to the SAME global physical
coordinates. Real tests are pulled back only to apply that producer. -/
theorem exists_step (s : StageState) (h : PhysicalTest) (Q : PhysicalJetData)
    {ε η κ ζ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ t : StageState, ∃ c : ℤ →₀ ℂ,
      t.δ < κ ∧ Q.Close ζ s.frame s.V t.frame t.V ∧
      dist s.vec t.vec < ε ∧ dist h.vec (t.laurent c) < Real.sqrt (2*s.δ)+η := by
  obtain ⟨τ,hr⟩ := s.reflected
  let h' := h.fn ∘ s.frame.chart.symm
  have hc : Continuous h' := h.fn.continuous.comp s.chart_symm_cont
  have hcen : ∫ x, h' x ∂tripleVolume=0 := by
    change ∫ x, h.fn (s.frame.chart.symm x) ∂tripleVolume=0
    rw [s.chart_symm_mp.integral_comp s.chartHomeo.symm.toMeasurableEquiv.measurableEmbedding,h.centered]
  obtain ⟨W,V,hp,hs,δ,l,u,α,P,c,hδ,hδ8,hδκ,hdl,hlu,hud,hv,hWs,hWr,hflat,
    hαc,hαm,hP,hjet,hFW,hHW⟩ := exists_one_stage s.packets hr s.δ_pos.le s.δ_half
      s.δ_l s.u_δ s.supported s.V s.periodic s.smooth s.increasing s.flat hc
      (fun x => h.real _) hcen (fun x => h.bound _) Q s.frame hε hη hκ hζ
  have hPc : Continuous P.chart := by
    rw [hP]; exact hαc.comp s.chart_cont
  have hPm : MeasurePreserving P.chart tripleVolume tripleVolume := by
    rw [hP]; exact hαm.comp s.chart_mp
  let t : StageState := {
    frame := P, chart_cont := hPc, chart_mp := hPm, packets := W,
    reflected := hWr, V := V, periodic := hp, smooth := hs,
    δ := δ, l := l, u := u, δ_pos := hδ, δ_half := by linarith,
    δ_l := hdl, l_u := hlu, u_δ := hud, increasing := hv, supported := hWs, flat := hflat }
  refine ⟨t,c,hδκ,hjet,?_,?_⟩
  · rw [← physicalDist_reps s.vec_ae t.vec_ae]
    change physicalDist (s.packets.vector ∘ s.frame.chart) (W.vector ∘ P.chart) < ε
    rw [hP]
    change physicalDist (s.packets.vector ∘ s.frame.chart) ((W.vector ∘ α) ∘ s.frame.chart) < ε
    rw [physicalDist_continuous_comp s.frame.chart s.chart_cont s.chart_mp]
    exact hFW
  · rw [← physicalDist_reps h.vec_ae (t.laurent_ae c)]
    change physicalDist h.fn (finitePacketLaurent (fun z => (hp.lift z:UnitAddCircle)) W.m W.A c ∘ P.chart) < _
    rw [hP]
    have he : (h.fn : TripleTorus → ℂ)=h' ∘ s.frame.chart := by
      funext x; exact congrArg h.fn (s.frame.chart.symm_apply_apply x).symm
    rw [he]
    change physicalDist (h' ∘ s.frame.chart)
      ((finitePacketLaurent (fun z => (hp.lift z:UnitAddCircle)) W.m W.A c ∘ α) ∘ s.frame.chart) < _
    rw [physicalDist_continuous_comp s.frame.chart s.chart_cont s.chart_mp]
    exact hHW

end StageState
end ThreeTorus
end
end

end OAI
