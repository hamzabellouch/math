import OAI.Probability.SLE.Gauge.UniformFrontPassage

namespace OAI

/-! The exact change of capacity clock in a first-front passage. Ordered
time changes preserve the stopped trace segment and its sausage, including
the attained first front and terminal offset. This applies to the positive
linear clocks arising from normalized Loewner charts. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.FrontClockChange
open FirstFrontPassage PassageSuccess

theorem firstFrontTime_of_clock_hit
    (e : ℝ≥0 ≃o ℝ≥0) (x : ℝ≥0 → ℝ) (q : ℝ) (τ : ℝ≥0)
    (hfirst : firstFrontTime (fun t => x (e t)) q = (τ : WithTop ℝ≥0))
    (hhit : x (e τ) = q) :
    firstFrontTime x q = (e τ : WithTop ℝ≥0) := by
  have hleast : IsLeast {t : ℝ≥0 | 0 ≤ t ∧ x t - q ∈ ({0} : Set ℝ)} (e τ) := by
    refine ⟨⟨bot_le, by simp only [hhit, sub_self, mem_singleton_iff]⟩, ?_⟩
    intro t ht
    have hh := hittingAfter_le_of_mem
      (u := fun s (_ : Unit) => x (e s) - q) (ω := ())
      (show (0 : ℝ≥0) ≤ e.symm t from bot_le)
      (show x (e (e.symm t)) - q ∈ ({0} : Set ℝ) by simpa only [e.apply_symm_apply] using ht.2)
    change firstFrontTime (fun s => x (e s)) q ≤ (e.symm t : WithTop ℝ≥0) at hh
    rw [hfirst, WithTop.coe_le_coe] at hh
    simpa only [e.apply_symm_apply] using e.monotone hh
  unfold firstFrontTime hittingAfter
  rw [ite_eq_left ⟨e τ, hleast.1⟩, hleast.csInf_eq]

theorem sourceSausageSet_clock
    (e : ℝ≥0 ≃o ℝ≥0) (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) (v : ℝ) :
    sourceSausageSet (fun u => γ (e u)) s t v = sourceSausageSet γ (e s) (e t) v := by
  ext z
  constructor
  · rintro ⟨u, hu, hd⟩
    exact ⟨e u, ⟨e.monotone hu.1, e.monotone hu.2⟩, hd⟩
  · rintro ⟨u, hu, hd⟩
    refine ⟨e.symm u, ⟨?_, ?_⟩, ?_⟩
    · exact (e.le_iff_le).mp (by simpa only [e.apply_symm_apply] using hu.1)
    · exact (e.le_iff_le).mp (by simpa only [e.apply_symm_apply] using hu.2)
    · simpa only [e.apply_symm_apply] using hd

theorem segmentSausageCharge_clock
    (e : ℝ≥0 ≃o ℝ≥0) (κ : ℝ) (γ : ℝ≥0 → ℂ)
    (s t : ℝ≥0) (v : ℝ) (R : Set ℂ) :
    segmentSausageCharge κ (fun u => γ (e u)) s t v R =
      segmentSausageCharge κ γ (e s) (e t) v R := by
  simp only [segmentSausageCharge, sourceSausageSet_clock]

theorem frontSuccess_clock_transport
    {Ω : Type*} (e : ℝ≥0 ≃o ℝ≥0) (η : Ω → ℝ≥0 → ℂ)
    (p : ℂ → ℝ) (σ : Ω → ℝ≥0) (V : Set ℂ) (a : ℂ) (ε : ℝ)
    (ω : Ω)
    (hω : ω ∈ FrontSuccess (fun _ ω t => η ω (e t)) (fun _ => p) σ
      (fun _ => V) (fun _ => a) ε 0) :
    ω ∈ FrontSuccess (fun _ => η) (fun _ => p) (fun ω => e (σ ω))
      (fun _ => V) (fun _ => a) ε 0 ∧
      frontTime (fun t => p (η ω t)) 1 =
        e (frontTime (fun t => p (η ω (e t))) 1) := by
  obtain ⟨hf, hh, hs, hpath, hend⟩ := hω
  let τ := frontTime (fun t => p (η ω (e t))) 1
  have hf' := firstFrontTime_of_clock_hit e (fun t => p (η ω t)) 1 τ hf hh
  have ht : frontTime (fun t => p (η ω t)) 1 = e τ := by
    simp only [frontTime, hf', WithTop.untopD_coe]
  refine ⟨?_, ht⟩
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [ht]
  refine ⟨hf', hh, e.strictMono hs, ?_, hend⟩
  intro t ht'
  have hmem : e.symm t ∈ Icc 0 τ := by
    refine ⟨bot_le, ?_⟩
    exact (e.le_iff_le).mp (by simpa only [e.apply_symm_apply] using ht'.2)
  simpa only [e.apply_symm_apply] using hpath hmem

theorem frontSuccess_clock_iff
    {Ω : Type*} (e : ℝ≥0 ≃o ℝ≥0) (η : Ω → ℝ≥0 → ℂ)
    (p : ℂ → ℝ) (σ : Ω → ℝ≥0) (V : Set ℂ) (a : ℂ) (ε : ℝ) (ω : Ω) :
    ω ∈ FrontSuccess (fun _ ω t => η ω (e t)) (fun _ => p)
        (fun ω => e.symm (σ ω)) (fun _ => V) (fun _ => a) ε 0 ↔
      ω ∈ FrontSuccess (fun _ => η) (fun _ => p) σ (fun _ => V) (fun _ => a) ε 0 := by
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using
      (frontSuccess_clock_transport e η p (fun ω => e.symm (σ ω)) V a ε ω h).1
  · intro h
    have hh : ω ∈ FrontSuccess
        (fun _ ω t => (fun u => η ω (e u)) (e.symm t))
        (fun _ => p) σ (fun _ => V) (fun _ => a) ε 0 := by
      simpa only [e.apply_symm_apply] using h
    exact (frontSuccess_clock_transport e.symm (fun ω t => η ω (e t)) p σ V a ε ω hh).1

/-- The full success-and-mass event is unchanged by capacity-clock
normalization. It is an exact event identity, before taking probabilities. -/
theorem frontSuccess_mass_clock
    {Ω : Type*} (e : ℝ≥0 ≃o ℝ≥0) (η : Ω → ℝ≥0 → ℂ)
    (p : ℂ → ℝ) (σ : Ω → ℝ≥0) (V : Set ℂ) (a : ℂ) (ε κ v c : ℝ) (R : Set ℂ) :
    {ω | ω ∈ FrontSuccess (fun _ ω t => η ω (e t)) (fun _ => p)
        (fun ω => e.symm (σ ω)) (fun _ => V) (fun _ => a) ε 0 ∧
      ENNReal.ofReal c ≤ segmentSausageCharge κ (fun t => η ω (e t))
        (e.symm (σ ω)) (frontTime (fun t => p (η ω (e t))) 1) v R} =
    {ω | ω ∈ FrontSuccess (fun _ => η) (fun _ => p) σ
        (fun _ => V) (fun _ => a) ε 0 ∧
      ENNReal.ofReal c ≤ segmentSausageCharge κ (η ω) (σ ω)
        (frontTime (fun t => p (η ω t)) 1) v R} := by
  ext ω
  constructor
  · rintro ⟨hs, hm⟩
    obtain ⟨hs', ht⟩ := frontSuccess_clock_transport e η p (fun ω => e.symm (σ ω))
      V a ε ω hs
    simp only [e.apply_symm_apply] at hs'
    refine ⟨hs', ?_⟩
    rw [segmentSausageCharge_clock, e.apply_symm_apply, ← ht] at hm
    exact hm
  · rintro ⟨hs, hm⟩
    have hs' := (frontSuccess_clock_iff e η p σ V a ε ω).mpr hs
    have ht := (frontSuccess_clock_transport e η p (fun ω => e.symm (σ ω))
      V a ε ω hs').2
    refine ⟨hs', ?_⟩
    rw [segmentSausageCharge_clock, e.apply_symm_apply, ← ht]
    exact hm

end SLEExactGauge.FrontClockChange

end

end OAI
