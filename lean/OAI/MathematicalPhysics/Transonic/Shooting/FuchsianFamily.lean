import OAI.MathematicalPhysics.Transonic.Shooting.FuchsianParametric

namespace OAI

section
noncomputable section

namespace SepticProfile.Fuchsian
open Set Filter Metric
open scoped Topology NNReal

/-- Uniform small-radius inversion and contraction constructs a continuously
parameterized family. In the source application H is the exact finite-jet
remainder map, whose bounds and continuity must be independently supplied. -/
theorem exists_continuous_fuchsian_disk {A : Type*} [TopologicalSpace A]
    (c : A → ℝ) (hc : Continuous c) (hc1 : ∀ a, 1 ≤ c a)
    {r R M L : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hrM : r*M ≤ R) (hrL : r*L ≤ 1/2)
    (H : A → analyticDisk → analyticDisk)
    (hbound : ∀ a f, ‖f‖ ≤ R → ‖H a f‖ ≤ M)
    (hlip : ∀ a f g, ‖f‖ ≤ R → ‖g‖ ≤ R → ‖H a f-H a g‖ ≤ L*‖f-g‖)
    (hcont : ∀ f, ‖f‖ ≤ R → Continuous (fun a => H a f))
    (P : Set analyticDisk) (hPc : IsClosed P) (hP0 : 0 ∈ P)
    (hP : ∀ a f, f ∈ P → ‖f‖ ≤ R → (r:ℂ) • inverse (c a) (H a f) ∈ P) :
    ∃ f : A → analyticDisk, Continuous f ∧ (∀ a, f a ∈ P ∧ ‖f a‖ ≤ R) ∧
      (∀ a, extend (f a : DiskMap) 0=0) ∧
      ∀ a z, z ∈ ball (0:ℂ) 1 →
        z*deriv (extend (f a : DiskMap)) z+(c a:ℂ)*extend (f a : DiskMap) z=
          (r:ℂ)*z*extend (H a (f a):DiskMap) z := by
  let T : A → analyticDisk → analyticDisk := fun a f => (r:ℂ) • inverse (c a) (H a f)
  have hc0 (a : A) : 0 ≤ c a := le_trans (by norm_num) (hc1 a)
  have hT (a : A) (f : analyticDisk) (hf : ‖f‖ ≤ R) : ‖T a f‖ ≤ R := by
    dsimp only [T]
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left ((norm_inverse_le (hc0 a) _).trans (hbound a f hf)) hr).trans hrM
  have hTd (a : A) (f g : analyticDisk) (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R) :
      ‖T a f-T a g‖ ≤ (1/2:ℝ)*‖f-g‖ := by
    dsimp only [T]
    rw [← smul_sub (r:ℂ) (inverse (c a) (H a f)) (inverse (c a) (H a g)),← inverse_sub (hc0 a),norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    calc
      _ ≤ r*(L*‖f-g‖) := mul_le_mul_of_nonneg_left
        ((norm_inverse_le (hc0 a) _).trans (hlip a f g hf hg)) hr
      _ ≤ _ := by rw [← mul_assoc];exact mul_le_mul_of_nonneg_right hrL (norm_nonneg _)
  let S : Set analyticDisk := closedBall 0 R ∩ P
  have hSc : IsClosed S := isClosed_closedBall.inter hPc
  let : CompleteSpace S := hSc.completeSpace_coe
  let zeroS : S := ⟨0,⟨mem_closedBall_zero_iff.mpr (by simpa using hR),hP0⟩⟩
  let : Nonempty S := ⟨zeroS⟩
  have hmaps (a : A) : MapsTo (T a) S S := by
    intro f hf
    exact ⟨mem_closedBall_zero_iff.mpr (hT a f (mem_closedBall_zero_iff.mp hf.1)),
      hP a f hf.2 (mem_closedBall_zero_iff.mp hf.1)⟩
  let TS (a : A) : S → S := (hmaps a).restrict (T a) S S
  have hcontract (a : A) : ContractingWith (1/2:ℝ≥0) (TS a) := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro f g
    change dist (T a f.val) (T a g.val) ≤ ((1/2:ℝ≥0):ℝ)*dist f.val g.val
    rw [dist_eq_norm,dist_eq_norm]
    exact hTd a f.val g.val (mem_closedBall_zero_iff.mp f.property.1)
      (mem_closedBall_zero_iff.mp g.property.1)
  let fS : A → S := fun a => (hcontract a).fixedPoint
  have hfix (a : A) : Function.IsFixedPt (TS a) (fS a) := (hcontract a).fixedPoint_isFixedPt
  have htcont (x : S) : Continuous (fun a => TS a x) := by
    apply Continuous.subtype_mk
    change Continuous (fun a => (r:ℂ) • inverse (c a) (H a x.val))
    exact (continuous_const : Continuous (fun _ : A => (r:ℂ))).smul (continuous_inverse_family c hc hc1
      (fun a => H a x.val) (hcont x.val (mem_closedBall_zero_iff.mp x.property.1)))
  have hfcont : Continuous fS := continuous_fixedPoint_family TS fS hcontract hfix htcont
  let f : A → analyticDisk := fun a => (fS a).val
  have hfix' (a : A) : T a (f a)=f a := congrArg Subtype.val (hfix a)
  have he (a : A) : extend (f a : DiskMap)=(r:ℂ) • extend (inverse (c a) (H a (f a)):DiskMap) := by
    calc
      _ = extend (T a (f a) :DiskMap) := congrArg (fun g : analyticDisk => extend (g:DiskMap)) (hfix' a).symm
      _ = _ := extend_smul _ _
  refine ⟨f,continuous_subtype_val.comp hfcont,?_,?_,?_⟩
  · intro a
    exact ⟨(fS a).property.2,mem_closedBall_zero_iff.mp (fS a).property.1⟩
  · intro a
    rw [he,Pi.smul_apply,inverse_zero,smul_zero]
  · intro a z hz
    rw [he,deriv_const_smul _ (differentiableAt_extend (inverse (c a) (H a (f a))) hz)]
    simp only [Pi.smul_apply,smul_eq_mul]
    have hi := inverse_ode (hc0 a) (H a (f a)) hz
    calc
      _ = (r:ℂ)*(z*deriv (extend (inverse (c a) (H a (f a)):DiskMap)) z+
        (c a:ℂ)*extend (inverse (c a) (H a (f a)):DiskMap) z) := by ring
      _ = _ := by rw [hi];ring

lemma continuous_nonlinearDisk_family {A : Type*} [TopologicalSpace A]
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (h : A → ℂ × ℂ → ℂ) (hdiff : ∀ a, DifferentiableOn ℂ (h a) (closedBall 0 R))
    (hcont : Continuous (fun p : A  ×  ↥(closedBall (0:ℂ × ℂ) R) => h p.1 p.2))
    (f : analyticDisk) (hf : ‖f‖ ≤ R) :
    Continuous (fun a => nonlinearDisk hr hrR (h a) (hdiff a) f) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have he : (fun p : A × Disk => (nonlinearDisk hr hrR (h p.1) (hdiff p.1) f : DiskMap) p.2)=
      (fun p : A × Disk => h p.1 ((r:ℂ)*(p.2:ℂ),(f:DiskMap) p.2)) := by
    funext p
    exact nonlinearDisk_apply hr hrR (h p.1) (hdiff p.1) f hf p.2
  change Continuous (fun p : A × Disk => (nonlinearDisk hr hrR (h p.1) (hdiff p.1) f : DiskMap) p.2)
  rw [he]
  exact hcont.comp (continuous_fst.prodMk
    (((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).prodMk
      ((f:DiskMap).continuous.comp continuous_snd)).subtype_mk
        (fun p => inputBound hr hrR f hf p.2)))

end SepticProfile.Fuchsian

end
end

end OAI
