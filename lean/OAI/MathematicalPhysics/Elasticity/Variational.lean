import OAI.MathematicalPhysics.Elasticity.Basic

namespace OAI

section
noncomputable section
open MeasureTheory Set
open scoped BigOperators



namespace Elasticity
open scoped BigOperators

lemma coordDeriv_add {f g : X → V} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : Fin 3) :
    coordDeriv (f+g) i = coordDeriv f i + coordDeriv g i := by
  funext x
  exact congrArg (fun L : X →L[ℝ] V => L (coordVector i))
    (fderiv_add (hf x) (hg x))

lemma coordDeriv_smul (c : ℝ) {f : X → V} (hf : Differentiable ℝ f)
    (i : Fin 3) : coordDeriv (c • f) i = c • coordDeriv f i := by
  funext x
  exact congrArg (fun L : X →L[ℝ] V => L (coordVector i))
    (fderiv_const_smul (hf x) c)

lemma coordDeriv_zero (i : Fin 3) : coordDeriv (0 : X → V) i = 0 := by
  ext x j
  simp [coordDeriv]

def smoothJetSubmodule (Ω : Set X) : Submodule ℝ (Ambient Ω) where
  carrier := SmoothJets Ω
  zero_mem' := by
    refine ⟨0, MemLp.zero, fun i => ?_, contDiff_const, ?_, ?_⟩
    · simpa only [coordDeriv_zero] using (MemLp.zero : MemLp (0 : X → V) 2 (volume.restrict Ω))
    · simp
    · funext i
      change 0 = _
      simp only [coordDeriv_zero, MemLp.toLp_zero]
  add_mem' := by
    rintro u v ⟨f, hf, hd, hs, hu, hud⟩ ⟨g, hg, he, ht, hv, hvd⟩
    have hb (i) : MemLp (coordDeriv (f+g) i) 2 (volume.restrict Ω) := by
      rw [coordDeriv_add (hs.differentiable (by simp)) (ht.differentiable (by simp))]
      exact (hd i).add (he i)
    refine ⟨f+g, hf.add hg, hb, hs.add ht, ?_, ?_⟩
    · simpa [hu, hv] using (MemLp.toLp_add hf hg).symm
    · funext i
      simp only [Prod.snd_add, Pi.add_apply, hud, hvd]
      simp only [coordDeriv_add (hs.differentiable (by simp)) (ht.differentiable (by simp))]
      exact (MemLp.toLp_add (hd i) (he i)).symm
  smul_mem' := by
    rintro c u ⟨f, hf, hd, hs, hu, hud⟩
    have hb (i) : MemLp (coordDeriv (c • f) i) 2 (volume.restrict Ω) := by
      rw [coordDeriv_smul c (hs.differentiable (by simp))]
      exact (hd i).const_smul c
    refine ⟨c • f, hf.const_smul c, hb, hs.const_smul c, ?_, ?_⟩
    · simpa [hu] using (MemLp.toLp_const_smul c hf).symm
    · funext i
      change c • u.2 i = _
      rw [hud]
      simp only [coordDeriv_smul c (hs.differentiable (by simp))]
      exact (MemLp.toLp_const_smul c (hd i)).symm

/-- Compactly supported interior test jets, with the actual support condition. -/
def testJetSubmodule (Ω : Set X) : Submodule ℝ (Ambient Ω) where
  carrier := TestJets Ω
  zero_mem' := by
    refine ⟨0, MemLp.zero, fun i => ?_, contDiff_const, HasCompactSupport.zero, ?_, ?_, ?_⟩
    · simpa only [coordDeriv_zero] using (MemLp.zero : MemLp (0 : X → V) 2 (volume.restrict Ω))
    · simp
    · simp
    · funext i
      change 0 = _
      simp only [coordDeriv_zero, MemLp.toLp_zero]
  add_mem' := by
    rintro u v ⟨f, hf, hd, hs, hc, hsup, hu, hud⟩ ⟨g, hg, he, ht, hgc, hgsup, hv, hvd⟩
    have hb (i) : MemLp (coordDeriv (f+g) i) 2 (volume.restrict Ω) := by
      rw [coordDeriv_add (hs.differentiable (by simp)) (ht.differentiable (by simp))]
      exact (hd i).add (he i)
    refine ⟨f+g, hf.add hg, hb, hs.add ht, hc.add hgc,
      (tsupport_add f g).trans (union_subset hsup hgsup), ?_, ?_⟩
    · simpa [hu, hv] using (MemLp.toLp_add hf hg).symm
    · funext i
      simp only [Prod.snd_add, Pi.add_apply, hud, hvd]
      simp only [coordDeriv_add (hs.differentiable (by simp)) (ht.differentiable (by simp))]
      exact (MemLp.toLp_add (hd i) (he i)).symm
  smul_mem' := by
    rintro c u ⟨f, hf, hd, hs, hc, hsup, hu, hud⟩
    have hb (i) : MemLp (coordDeriv (c • f) i) 2 (volume.restrict Ω) := by
      rw [coordDeriv_smul c (hs.differentiable (by simp))]
      exact (hd i).const_smul c
    refine ⟨c • f, hf.const_smul c, hb, hs.const_smul c, (hc.smul_left : HasCompactSupport ((fun _ : X => c) • f)),
      (tsupport_smul_subset_right (fun _ : X => c) f).trans hsup, ?_, ?_⟩
    · simpa [hu] using (MemLp.toLp_const_smul c hf).symm
    · funext i
      change c • u.2 i = _
      rw [hud]
      simp only [coordDeriv_smul c (hs.differentiable (by simp))]
      exact (MemLp.toLp_const_smul c (hd i)).symm

lemma testJetSubmodule_le (Ω : Set X) : testJetSubmodule Ω ≤ smoothJetSubmodule Ω := by
  rintro u ⟨f,hf,hd,hs,_,_,hu,hud⟩
  exact ⟨f,hf,hd,hs,hu,hud⟩

def h1Submodule (Ω : Set X) : Submodule ℝ (Ambient Ω) :=
  (smoothJetSubmodule Ω).topologicalClosure

def h10Submodule (Ω : Set X) : Submodule ℝ (Ambient Ω) :=
  (testJetSubmodule Ω).topologicalClosure

lemma h10Submodule_le (Ω : Set X) : h10Submodule Ω ≤ h1Submodule Ω :=
  Submodule.topologicalClosure_mono (testJetSubmodule_le Ω)

lemma sameTrace_refl (Ω : Set X) (u : H1 Ω) : SameTrace Ω u u := by
  exact show u.val - u.val ∈ h10Submodule Ω by rw [sub_self]; exact Submodule.zero_mem _

lemma sameTrace_symm (Ω : Set X) {u v : H1 Ω} (h : SameTrace Ω u v) :
    SameTrace Ω v u := by
  exact show v.val - u.val ∈ h10Submodule Ω by
    rw [← neg_sub]; exact Submodule.neg_mem _ h

lemma sameTrace_trans (Ω : Set X) {u v w : H1 Ω}
    (h : SameTrace Ω u v) (h' : SameTrace Ω v w) : SameTrace Ω u w := by
  exact show u.val - w.val ∈ h10Submodule Ω by
    convert Submodule.add_mem (h10Submodule Ω) h h' using 1; abel

abbrev JetH (Ω : Set X) := PiLp 2 (fun _ : Option (Fin 3) => Lp V 2 (volume.restrict Ω))

def jetEquiv (Ω : Set X) : JetH Ω ≃L[ℝ] Ambient Ω := by
  let e : (Option (Fin 3) → Lp V 2 (volume.restrict Ω)) ≃L[ℝ] Ambient Ω :=
    { toLinearEquiv := LinearEquiv.piOptionEquivProd ℝ
      continuous_toFun := (continuous_apply none).prodMk
        (continuous_pi fun i => continuous_apply (some i))
      continuous_invFun := continuous_pi fun i => by
        cases i with
        | none => exact continuous_fst
        | some i => exact (continuous_apply i).comp continuous_snd }
  exact (PiLp.continuousLinearEquiv 2 ℝ _).trans e

@[simp] lemma jetEquiv_apply (Ω : Set X) (u : JetH Ω) :
    jetEquiv Ω u = (u none, fun i => u (some i)) := rfl

def H1Hilbert (Ω : Set X) : Submodule ℝ (JetH Ω) :=
  (h1Submodule Ω).comap (jetEquiv Ω).toLinearMap

def H10Hilbert (Ω : Set X) : Submodule ℝ (JetH Ω) :=
  (h10Submodule Ω).comap (jetEquiv Ω).toLinearMap

lemma isClosed_H1Hilbert (Ω : Set X) : IsClosed (H1Hilbert Ω : Set (JetH Ω)) :=
  (smoothJetSubmodule Ω).isClosed_topologicalClosure.preimage (jetEquiv Ω).continuous

lemma isClosed_H10Hilbert (Ω : Set X) : IsClosed (H10Hilbert Ω : Set (JetH Ω)) :=
  (testJetSubmodule Ω).isClosed_topologicalClosure.preimage (jetEquiv Ω).continuous

instance (Ω : Set X) : CompleteSpace (H1Hilbert Ω) := (isClosed_H1Hilbert Ω).completeSpace_coe
instance (Ω : Set X) : CompleteSpace (H10Hilbert Ω) := (isClosed_H10Hilbert Ω).completeSpace_coe

lemma H10Hilbert_le (Ω : Set X) : H10Hilbert Ω ≤ H1Hilbert Ω :=
  Submodule.comap_mono (h10Submodule_le Ω)

/-- The Hilbert version is exactly the H¹ jet closure, not an extra
regularity hypothesis or a replacement by a smaller test space. -/
def h1Equiv (Ω : Set X) : (H1Hilbert Ω) ≃ H1 Ω where
  toFun u := ⟨jetEquiv Ω u, u.property⟩
  invFun u := ⟨(jetEquiv Ω).symm u.val, by
    change jetEquiv Ω ((jetEquiv Ω).symm u.val) ∈ h1Submodule Ω
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact u.property⟩
  left_inv u := by apply Subtype.ext; exact (jetEquiv Ω).symm_apply_apply u.val
  right_inv u := by apply Subtype.ext; exact (jetEquiv Ω).apply_symm_apply u.val

end Elasticity

end
end
section
/-! The physical energy is a continuous bilinear form on the actual
Hilbert jet space. Bounded coefficients below are proved from admissibility
later, rather than added to the inverse theorem. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Elasticity

abbrev ScalarL2 (Ω : Set X) := Lp ℝ 2 (volume.restrict Ω)

structure BoundedCoefficient (Ω : Set X) (a : X → ℝ) : Prop where
  measurable : AEStronglyMeasurable a (volume.restrict Ω)
  bound : ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict Ω), ‖a x‖ ≤ C

namespace BoundedCoefficient
variable {Ω : Set X} {a : X → ℝ} (ha : BoundedCoefficient Ω a)

include ha in
lemma mul_memLp (f : ScalarL2 Ω) : MemLp (fun x => a x * f x) 2 (volume.restrict Ω) := by
  obtain ⟨C,hC⟩ := ha.bound
  apply (Lp.memLp f).of_le_mul (c := C) (ha.measurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with x hx
  simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

def mulL : ScalarL2 Ω →L[ℝ] ScalarL2 Ω := by
  let F : ScalarL2 Ω →ₗ[ℝ] ScalarL2 Ω :=
    { toFun f := (ha.mul_memLp f).toLp _
      map_add' f g := by
        apply Lp.ext
        filter_upwards [(ha.mul_memLp (f+g)).coeFn_toLp,
          (ha.mul_memLp f).coeFn_toLp, (ha.mul_memLp g).coeFn_toLp,
          Lp.coeFn_add f g, Lp.coeFn_add ((ha.mul_memLp f).toLp _) ((ha.mul_memLp g).toLp _)]
          with x hfg hf hg hadd he
        rw [hfg,he]
        simp only [Pi.add_apply]
        rw [hf,hg,hadd]
        exact mul_add ..
      map_smul' c f := by
        apply Lp.ext
        filter_upwards [(ha.mul_memLp (c • f)).coeFn_toLp,
          (ha.mul_memLp f).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((ha.mul_memLp f).toLp _)] with x hcf hf hs ht
        simp only [RingHom.id_apply]
        rw [hcf,ht]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hf,hs]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring }
  let C := ha.bound.choose
  have hC := ha.bound.choose_spec
  exact F.mkContinuous C (fun f => by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(ha.mul_memLp f).coeFn_toLp,hC] with x hx hb
    change ‖(ha.mul_memLp f).toLp _ x‖ ≤ _
    rw [hx,norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma mulL_ae (f : ScalarL2 Ω) : ha.mulL f =ᵐ[volume.restrict Ω] fun x => a x*f x :=
  (ha.mul_memLp f).coeFn_toLp

lemma inner_mulL (f g : ScalarL2 Ω) :
    inner ℝ (ha.mulL f) g = ∫ x, a x*f x*g x ∂(volume.restrict Ω) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha.mulL_ae f] with x hx
  rw [hx,real_inner_comm]
  rfl
end BoundedCoefficient

variable {Ω : Set X}

lemma lp_sum_ae {ι : Type*} (s : Finset ι) (f : ι → ScalarL2 Ω) :
    ((∑ i ∈ s, f i : ScalarL2 Ω) : X → ℝ) =ᵐ[volume.restrict Ω] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
    exact hx
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx hy
    simp only [Pi.add_apply] at hx
    exact hx.trans (congrArg (fun t => f i x+t) hy)

def jetEntry (Ω : Set X) (i j : Fin 3) : JetH Ω →L[ℝ] ScalarL2 Ω :=
  ((EuclideanSpace.proj i).compLpL 2 (volume.restrict Ω)).comp
    (PiLp.proj 2 (fun _ : Option (Fin 3) => Lp V 2 (volume.restrict Ω)) (some j))

def jetDiv (Ω : Set X) : JetH Ω →L[ℝ] ScalarL2 Ω := ∑ i, jetEntry Ω i i

def jetStrain (Ω : Set X) (i j : Fin 3) : JetH Ω →L[ℝ] ScalarL2 Ω :=
  (1/2 : ℝ) • (jetEntry Ω i j + jetEntry Ω j i)

lemma jetEntry_ae (u : JetH Ω) (i j : Fin 3) :
    jetEntry Ω i j u =ᵐ[volume.restrict Ω] fun x => (u (some j) x) i :=
  ContinuousLinearMap.coeFn_compLpL _ _

lemma jetDiv_ae (u : JetH Ω) :
    jetDiv Ω u =ᵐ[volume.restrict Ω] fun x => ∑ i, (u (some i) x) i := by
  have hs := lp_sum_ae Finset.univ (fun i => jetEntry Ω i i u)
  have he : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, jetEntry Ω i i u x = (u (some i) x) i :=
    Filter.eventually_all.mpr (fun i => jetEntry_ae u i i)
  filter_upwards [hs,he] with x hx hy
  change (∑ i, jetEntry Ω i i) u x = _
  simpa only [sum_apply,hy] using hx

lemma jetStrain_ae (u : JetH Ω) (i j : Fin 3) :
    jetStrain Ω i j u =ᵐ[volume.restrict Ω]
      fun x => ((u (some j) x) i+(u (some i) x) j)/2 := by
  filter_upwards [Lp.coeFn_smul (1/2 : ℝ) (jetEntry Ω i j u+jetEntry Ω j i u),
    Lp.coeFn_add (jetEntry Ω i j u) (jetEntry Ω j i u),
    jetEntry_ae u i j, jetEntry_ae u j i] with x hs ha hi hj
  change ((1/2 : ℝ) • (jetEntry Ω i j u+jetEntry Ω j i u)) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [ha]
  simp only [Pi.add_apply,hi,hj]
  ring

def jetEnergy {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) : JetH Ω →L[ℝ] JetH Ω →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (hl.mulL.comp (jetDiv Ω)) (jetDiv Ω) +
    (2 : ℝ) • ∑ i, ∑ j, (innerSL ℝ).bilinearComp
      (hm.mulL.comp (jetStrain Ω i j)) (jetStrain Ω i j)

lemma jetEnergy_apply {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v : JetH Ω) :
    jetEnergy hl hm u v = inner ℝ (hl.mulL (jetDiv Ω u)) (jetDiv Ω v) +
      2 * ∑ i, ∑ j, inner ℝ (hm.mulL (jetStrain Ω i j u)) (jetStrain Ω i j v) := by
  simp [jetEnergy,sum_apply,ContinuousLinearMap.bilinearComp_apply,
    innerSL_apply_apply]

end Elasticity

end
end
section
/-! Actual Korn and supported Poincaré identities, needed for variational
wellposedness of the physical DN map. No coercivity is assumed. -/
noncomputable section
open MeasureTheory SchwartzMap
open scoped BigOperators LineDeriv SchwartzMap
namespace ElasticityKorn
abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev S := SchwartzMap X ℝ
abbrev L2 : S →L[ℝ] Lp ℝ 2 (volume : Measure X) := SchwartzMap.toLpCLM ℝ ℝ 2 volume

def norm2 (f : S) := ‖L2 f‖
def pair (f g : S) : ℝ := inner ℝ (L2 f) (L2 g)
def e (i : Fin 3) : X := EuclideanSpace.single i 1
def d (v : X) : S →ₗ[ℝ] S := (LineDeriv.lineDerivOpCLM ℝ S v).toLinearMap
@[simp] lemma d_apply (v : X) (f : S) (x : X) :
    d v f x = fderiv ℝ (f : X → ℝ) x v := rfl
lemma smooth (f : S) : ContDiff ℝ (⊤ : ℕ∞) (f : X → ℝ) := f.smooth _
lemma pair_integral (f g : S) : pair f g = ∫ x : X, f x * g x := by
  rw [pair, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hx hy
  change inner ℝ (f.toLp 2 volume x) (g.toLp 2 volume x) = _
  rw [hx, hy]
  exact real_inner_comm _ _

lemma pair_self (f : S) : pair f f = norm2 f ^ 2 := real_inner_self_eq_norm_sq _
lemma pair_symm (f g : S) : pair f g = pair g f := real_inner_comm _ _
lemma pair_add_left (f g h : S) : pair (f+g) h = pair f h + pair g h := by
  simp only [pair, map_add, inner_add_left]
lemma pair_add_right (f g h : S) : pair f (g+h) = pair f g + pair f h := by
  simp only [pair, map_add, inner_add_right]
lemma pair_smul_left (c : ℝ) (f g : S) : pair (c • f) g = c * pair f g := by
  simp only [pair, map_smul, real_inner_smul_left]
lemma pair_smul_right (c : ℝ) (f g : S) : pair f (c • g) = c * pair f g := by
  simp only [pair, map_smul, real_inner_smul_right]
lemma pair_sum_left {ι : Type*} (s : Finset ι) (f : ι → S) (g : S) :
    pair (∑ i ∈ s, f i) g = ∑ i ∈ s, pair (f i) g := by
  simp only [pair, map_sum, sum_inner]
lemma pair_sum_right {ι : Type*} (s : Finset ι) (f : S) (g : ι → S) :
    pair f (∑ i ∈ s, g i) = ∑ i ∈ s, pair f (g i) := by
  simp only [pair, map_sum, inner_sum]
lemma pair_bound (f g : S) : |pair f g| ≤ norm2 f * norm2 g := abs_real_inner_le_norm _ _
lemma integrable_pair (f g : S) : Integrable (fun x : X => f x*g x) :=
  (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f g).integrable
lemma pair_d (f g : S) (v : X) : pair f (d v g) = -pair (d v f) g := by
  simp only [pair_integral]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_pair (d v f) g) (integrable_pair f (d v g)) (integrable_pair f g)
    (fun x _ => (smooth f).differentiable (by simp) x)
    (fun x _ => (smooth g).differentiable (by simp) x)
lemma d_d (v w : X) (f : S) (x : X) :
    d v (d w f) x = fderiv ℝ (fderiv ℝ (f : X → ℝ)) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ (f : X → ℝ)) :=
    ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : X → ℝ) y w) x v = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp
lemma d_comm (v w : X) (f : S) : d v (d w f) = d w (d v f) := by
  ext x
  rw [d_d, d_d]
  exact (smooth f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _
lemma cross (v w : X) (f g : S) : pair (d v f) (d w g) = pair (d w f) (d v g) := by
  have h := pair_d (d v f) g w
  have h' := pair_d (d w f) g v
  rw [d_comm] at h
  exact h.trans h'.symm

def divergence (u : Fin 3 → S) : S := ∑ i, d (e i) (u i)
def gradEnergy (u : Fin 3 → S) : ℝ := ∑ i, ∑ j, norm2 (d (e i) (u j)) ^ 2
def strainEnergy (u : Fin 3 → S) : ℝ :=
  ∑ i, ∑ j, norm2 ((1/2 : ℝ) • (d (e i) (u j) + d (e j) (u i))) ^ 2
lemma norm2_half_add_sq (f g : S) :
    norm2 ((1/2 : ℝ) • (f+g)) ^ 2 = (norm2 f ^ 2 + 2*pair f g + norm2 g ^ 2)/4 := by
  rw [← pair_self, pair_smul_left, pair_smul_right, pair_add_left,
    pair_add_right, pair_add_right, pair_self, pair_self, pair_symm g f]
  ring
lemma cross_sum (u : Fin 3 → S) :
    (∑ i, ∑ j, pair (d (e i) (u j)) (d (e j) (u i))) = norm2 (divergence u) ^ 2 := by
  rw [← pair_self, divergence, pair_sum_left]
  simp_rw [pair_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cross]
  exact pair_symm _ _
/-- The classical exact whole-space Korn identity, by two integrations by parts. -/
theorem korn_identity (u : Fin 3 → S) :
    2*strainEnergy u = gradEnergy u + norm2 (divergence u)^2 := by
  simp only [strainEnergy, norm2_half_add_sq, add_div, mul_div_assoc]
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  have hs : (∑ i, ∑ j, norm2 (d (e j) (u i))^2) = gradEnergy u := Finset.sum_comm
  simp_rw [← Finset.sum_div]
  rw [hs, cross_sum u]
  change 2*((gradEnergy u/4 + 2*(norm2 (divergence u)^2/4)) + gradEnergy u/4) = _
  ring

theorem korn (u : Fin 3 → S) : gradEnergy u ≤ 2*strainEnergy u := by
  rw [korn_identity]
  exact le_add_of_nonneg_right (sq_nonneg _)

def qCLM : X →L[ℝ] ℝ := EuclideanSpace.proj 0
def Q : S →ₗ[ℝ] S := (SchwartzMap.smulLeftCLM ℝ qCLM).toLinearMap
@[simp] lemma Q_apply (f : S) (x : X) : Q f x = x 0 * f x :=
  SchwartzMap.smulLeftCLM_apply_apply qCLM.hasTemperateGrowth f x
lemma d_Q (f : S) : d (e 0) (Q f) = f + Q (d (e 0) f) := by
  ext x
  rw [d_apply]
  have hc : (Q f : X → ℝ) = fun x => x 0 * f x := by ext x; exact Q_apply f x
  rw [hc]
  change _ = f x + Q (d (e 0) f) x
  rw [Q_apply, d_apply]
  have h := congrArg (fun L : X →L[ℝ] ℝ => L (e 0))
    (((EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt (x := x)).mul
      ((smooth f).differentiable (by simp) x).hasFDerivAt).fderiv
  simpa [e, add_comm, Pi.mul_def] using h
lemma pair_Q (f g : S) : pair f (Q g) = pair (Q f) g := by
  simp only [pair_integral, Q_apply]
  congr 1
  ext x
  ring
lemma norm2_Q_supported {R : ℝ} (f : S) (hf : ∀ x, f x ≠ 0 → |x 0| ≤ R) :
    norm2 (Q f) ≤ R*norm2 f := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(Q f).coeFn_toLp 2 volume, f.coeFn_toLp 2 volume] with x hx hy
  change ‖(Q f).toLp 2 volume x‖ ≤ R*‖f.toLp 2 volume x‖
  rw [hx, hy, Q_apply, norm_mul, Real.norm_eq_abs]
  by_cases hz : f x=0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (hf x hz) (norm_nonneg _)
/-- Supported Poincaré with explicit constant; support is imposed on the actual
function, not on an abstract or assumed Sobolev norm. -/
theorem poincare {R : ℝ} (f : S) (hf : ∀ x, f x ≠ 0 → |x 0| ≤ R) :
    norm2 f ≤ 2*R*norm2 (d (e 0) f) := by
  have he := pair_d (Q f) f (e 0)
  rw [d_Q, pair_add_left, pair_self, pair_symm (Q (d (e 0) f)) f, pair_Q] at he
  have ht := pair_bound (Q f) (d (e 0) f)
  have hq := norm2_Q_supported f hf
  have hnn : 0 ≤ norm2 (d (e 0) f) := norm_nonneg _
  have hn : 0 ≤ norm2 f := norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hq hnn
  by_cases hzero : norm2 f = 0
  · rw [hzero]
    by_cases hR : 0 ≤ R
    · positivity
    · have hz : f=0 := by
        apply SchwartzMap.injective_toLp 2 volume
        change L2 f = L2 0
        rw [map_zero]
        exact norm_eq_zero.mp hzero
      rw [hz, map_zero]
      change 0 ≤ 2*R*‖L2 0‖
      rw [map_zero, norm_zero, mul_zero]
  · have hp : 0 < norm2 f := lt_of_le_of_ne hn (Ne.symm hzero)
    have ha := neg_le_abs (pair (Q f) (d (e 0) f))
    nlinarith

end ElasticityKorn

end
end
section
noncomputable section
open MeasureTheory SchwartzMap Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}

instance temperate_restrict_volume (Ω : Set X) : (volume.restrict Ω).HasTemperateGrowth :=
  ⟨⟨volume.integrablePower,
    (Measure.integrable_pow_neg_integrablePower (volume : Measure X)).mono_measure
      Measure.restrict_le_self⟩⟩

abbrev schwartzR (Ω : Set X) : SchwartzMap X ℝ →L[ℝ] ScalarL2 Ω :=
  SchwartzMap.toLpCLM ℝ ℝ 2 (volume.restrict Ω)

lemma schwartzR_norm_sq (f : SchwartzMap X ℝ) :
    ‖schwartzR Ω f‖^2 = ∫ x, (f x)^2 ∂(volume.restrict Ω) := by
  rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 (volume.restrict Ω)] with x hx
  change inner ℝ (f.toLp 2 (volume.restrict Ω) x) (f.toLp 2 (volume.restrict Ω) x) = _
  rw [hx,real_inner_comm]
  exact (sq _).symm

lemma schwartzR_supported_norm (f : SchwartzMap X ℝ) (hf : tsupport (f : X → ℝ) ⊆ Ω) :
    ‖schwartzR Ω f‖ = ElasticityKorn.norm2 f := by
  have hsq : ‖schwartzR Ω f‖^2 = ElasticityKorn.norm2 f^2 := by
    rw [schwartzR_norm_sq,← ElasticityKorn.pair_self,ElasticityKorn.pair_integral]
    simp only [← sq]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : f x=0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hf ht))
    simp [hz]
  have hnon : 0 ≤ ElasticityKorn.norm2 f := norm_nonneg _
  nlinarith [norm_nonneg (schwartzR Ω f)]

def jetScalar (Ω : Set X) (k : Option (Fin 3)) (i : Fin 3) :
    JetH Ω →L[ℝ] ScalarL2 Ω :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω)).comp
    (PiLp.proj 2 (fun _ : Option (Fin 3) => Lp V 2 (volume.restrict Ω)) k)

lemma jetScalar_ae (u : JetH Ω) (k : Option (Fin 3)) (i : Fin 3) :
    jetScalar Ω k i u =ᵐ[volume.restrict Ω] fun x => (u k x) i :=
  ContinuousLinearMap.coeFn_compLpL _ _

lemma scalar_projection_norm_sq (u : Lp V 2 (volume.restrict Ω)) :
    ‖u‖^2 = ∑ i, ‖(EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) u‖^2 := by
  let F (i : Fin 3) : ScalarL2 Ω := (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) u
  have hmeas (i : Fin 3) : Integrable (fun x => (F i x)^2) (volume.restrict Ω) := by
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using (L2.integrable_inner (𝕜 := ℝ) (F i) (F i))
  have hnorm (i : Fin 3) : ‖F i‖^2 = ∫ x, (F i x)^2 ∂(volume.restrict Ω) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  change ‖u‖^2 = ∑ i, ‖F i‖^2
  simp_rw [hnorm]
  rw [← integral_finsetSum Finset.univ (fun i _ => hmeas i),← real_inner_self_eq_norm_sq,
    L2.inner_def]
  have he : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, F i x=(u x) i :=
    Filter.eventually_all.mpr (fun i => ContinuousLinearMap.coeFn_compLpL _ u)
  apply integral_congr_ae
  filter_upwards [he] with x hx
  simp only [hx,real_inner_self_eq_norm_sq,EuclideanSpace.real_norm_sq_eq]

def jetValueSq (Ω : Set X) (u : JetH Ω) : ℝ := ∑ i, ‖jetScalar Ω none i u‖^2
def jetGradSq (Ω : Set X) (u : JetH Ω) : ℝ := ∑ i, ∑ j, ‖jetEntry Ω i j u‖^2
def jetStrainSq (Ω : Set X) (u : JetH Ω) : ℝ := ∑ i, ∑ j, ‖jetStrain Ω i j u‖^2

lemma jet_norm_sq (u : JetH Ω) : ‖u‖^2 = jetValueSq Ω u+jetGradSq Ω u := by
  rw [PiLp.norm_sq_eq_of_L2,Fintype.sum_option]
  simp_rw [scalar_projection_norm_sq]
  change jetValueSq Ω u+ (∑ j, ∑ i, ‖jetEntry Ω i j u‖^2) = _
  rw [Finset.sum_comm]
  rfl

lemma continuous_jetValueSq : Continuous (jetValueSq Ω) := by
  unfold jetValueSq
  fun_prop
lemma continuous_jetGradSq : Continuous (jetGradSq Ω) := by
  unfold jetGradSq
  fun_prop
lemma continuous_jetStrainSq : Continuous (jetStrainSq Ω) := by
  unfold jetStrainSq
  fun_prop

/-- The scalar derivatives of an actual vector-valued smooth test field. -/
lemma coordDeriv_scalar (f : X → V) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin 3) (x : X) :
    fderiv ℝ (fun y => (f y) i) x (coordVector j) = (coordDeriv f j x) i := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := f x)).comp x
    ((hf.differentiable (by simp) x).hasFDerivAt)
  change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ f) x (coordVector j) = _
  rw [h.fderiv]
  rfl

lemma scalar_test_support (f : X → V) (i : Fin 3) :
    tsupport (fun x => (f x) i) ⊆ tsupport f :=
  tsupport_comp_subset (g := fun y : V => y i) rfl f

lemma jet_test_representation (u : JetH Ω) (hu : jetEquiv Ω u ∈ TestJets Ω) :
    ∃ F : Fin 3 → SchwartzMap X ℝ,
      (∀ i, tsupport (F i : X → ℝ) ⊆ Ω) ∧
      (∀ i, jetScalar Ω none i u = schwartzR Ω (F i)) ∧
      ∀ i j, jetEntry Ω i j u = schwartzR Ω (ElasticityKorn.d (ElasticityKorn.e j) (F i)) := by
  obtain ⟨f,hf,hd,hs,hc,hsub,hu,hud⟩ := hu
  let F (i : Fin 3) : SchwartzMap X ℝ :=
    ((hc.comp_left (g := fun y : V => y i) rfl)).toSchwartzMap
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)
  have hF (i) (x : X) : F i x=(f x) i := rfl
  refine ⟨F,fun i => (scalar_test_support f i).trans hsub,?_,?_⟩
  · intro i
    apply Lp.ext
    have hv : (u none : X → V) =ᵐ[volume.restrict Ω] f := by
      change (jetEquiv Ω u).1 =ᵐ[volume.restrict Ω] f
      rw [hu]
      exact hf.coeFn_toLp
    filter_upwards [jetScalar_ae u none i,hv,(F i).coeFn_toLp 2 (volume.restrict Ω)] with x hx hy hz
    exact hx.trans ((congrArg (fun y : V => y i) hy).trans hz.symm)
  · intro i j
    apply Lp.ext
    have hv : (u (some j) : X → V) =ᵐ[volume.restrict Ω] coordDeriv f j := by
      change (jetEquiv Ω u).2 j =ᵐ[volume.restrict Ω] coordDeriv f j
      rw [hud]
      exact (hd j).coeFn_toLp
    filter_upwards [jetEntry_ae u i j,hv,
      (ElasticityKorn.d (ElasticityKorn.e j) (F i)).coeFn_toLp 2 (volume.restrict Ω)] with x hx hy hz
    change jetEntry Ω i j u x = (ElasticityKorn.d (ElasticityKorn.e j) (F i)).toLp 2 (volume.restrict Ω) x
    rw [hz,ElasticityKorn.d_apply]
    change jetEntry Ω i j u x = fderiv ℝ (fun y => (f y) i) x (coordVector j)
    rw [coordDeriv_scalar f hs i j x,hx,hy]

end Elasticity

end
end
section
noncomputable section
open MeasureTheory SchwartzMap Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}

lemma schwartz_d_support (f : SchwartzMap X ℝ) (v : X) :
    tsupport (ElasticityKorn.d v f : X → ℝ) ⊆ tsupport (f : X → ℝ) :=
  tsupport_fderiv_apply_subset ℝ v

lemma schwartz_strain_support (f g : SchwartzMap X ℝ) (v w : X)
    (hf : tsupport (f : X → ℝ) ⊆ Ω) (hg : tsupport (g : X → ℝ) ⊆ Ω) :
    tsupport (((1/2 : ℝ) • (ElasticityKorn.d v f+ElasticityKorn.d w g)) : X → ℝ) ⊆ Ω := by
  exact (tsupport_smul_subset_right (fun _ : X => (1/2 : ℝ)) _).trans
    ((tsupport_add _ _).trans (union_subset ((schwartz_d_support f v).trans hf)
      ((schwartz_d_support g w).trans hg)))

lemma jet_test_energies (u : JetH Ω) (hu : jetEquiv Ω u ∈ TestJets Ω) :
    ∃ F : Fin 3 → SchwartzMap X ℝ,
      (∀ i, tsupport (F i : X → ℝ) ⊆ Ω) ∧
      jetValueSq Ω u = ∑ i, ElasticityKorn.norm2 (F i)^2 ∧
      jetGradSq Ω u = ElasticityKorn.gradEnergy F ∧
      jetStrainSq Ω u = ElasticityKorn.strainEnergy F := by
  obtain ⟨F,hF,hval,hgrad⟩ := jet_test_representation u hu
  refine ⟨F,hF,?_,?_,?_⟩
  · unfold jetValueSq
    simp_rw [hval]
    congr 1
    funext i
    rw [schwartzR_supported_norm _ (hF i)]
  · unfold jetGradSq ElasticityKorn.gradEnergy
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hgrad,schwartzR_supported_norm _ ((schwartz_d_support _ _).trans (hF j))]
  · unfold jetStrainSq ElasticityKorn.strainEnergy
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change ‖(1/2 : ℝ) • (jetEntry Ω i j u+jetEntry Ω j i u)‖^2 = _
    rw [hgrad,hgrad,← map_add,← map_smul]
    rw [schwartzR_supported_norm _ (schwartz_strain_support _ _ _ _ (hF i) (hF j)),add_comm]

lemma test_korn (u : JetH Ω) (hu : jetEquiv Ω u ∈ TestJets Ω) :
    jetGradSq Ω u ≤ 2*jetStrainSq Ω u := by
  obtain ⟨F,_,_,hg,hs⟩ := jet_test_energies u hu
  rw [hg,hs]
  exact ElasticityKorn.korn F

lemma test_poincare {R : ℝ} (hR : 0 < R) (hbound : ∀ x ∈ Ω, |x 0| ≤ R)
    (u : JetH Ω) (hu : jetEquiv Ω u ∈ TestJets Ω) :
    jetValueSq Ω u ≤ 4*R^2*jetGradSq Ω u := by
  obtain ⟨F,hF,hv,hg,_⟩ := jet_test_energies u hu
  rw [hv,hg,ElasticityKorn.gradEnergy,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp := ElasticityKorn.poincare (F i) (fun x hx =>
    hbound x (hF i (subset_tsupport _ hx)))
  have hsq : ElasticityKorn.norm2 (F i)^2 ≤
      4*R^2*ElasticityKorn.norm2 (ElasticityKorn.d (ElasticityKorn.e 0) (F i))^2 := by
    have := sq_le_sq₀ (norm_nonneg (ElasticityKorn.L2 (F i)))
      (show 0 ≤ 2*R*ElasticityKorn.norm2 (ElasticityKorn.d (ElasticityKorn.e 0) (F i)) by
        exact mul_nonneg (by positivity) (norm_nonneg _))
    have ht : ElasticityKorn.norm2 (F i)^2 ≤
        (2*R*ElasticityKorn.norm2 (ElasticityKorn.d (ElasticityKorn.e 0) (F i)))^2 := this.mpr hp
    nlinarith [ht]
  refine hsq.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg (ElasticityKorn.norm2 (ElasticityKorn.d (ElasticityKorn.e j) (F i))))
    (Finset.mem_univ (0 : Fin 3))

lemma h10_induction_closed {P : JetH Ω → Prop} (hP : IsClosed {u | P u})
    (htest : ∀ u, jetEquiv Ω u ∈ TestJets Ω → P u)
    (u : H10Hilbert Ω) : P u := by
  have hclosed : IsClosed {v : Ambient Ω | P ((jetEquiv Ω).symm v)} :=
    hP.preimage (jetEquiv Ω).symm.continuous
  have hsubset : closure (TestJets Ω) ⊆ {v : Ambient Ω | P ((jetEquiv Ω).symm v)} :=
    closure_minimal (fun v hv => htest _ (by simpa using hv)) hclosed
  have h := hsubset u.property
  change P ((jetEquiv Ω).symm (jetEquiv Ω u.val)) at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

lemma h10_korn (u : H10Hilbert Ω) : jetGradSq Ω u ≤ 2*jetStrainSq Ω u := by
  apply h10_induction_closed
    (isClosed_le continuous_jetGradSq (continuous_const.mul continuous_jetStrainSq))
    test_korn u

lemma h10_poincare {R : ℝ} (hR : 0 < R) (hbound : ∀ x ∈ Ω, |x 0| ≤ R)
    (u : H10Hilbert Ω) : jetValueSq Ω u ≤ 4*R^2*jetGradSq Ω u := by
  apply h10_induction_closed
    (isClosed_le continuous_jetValueSq (continuous_const.mul continuous_jetGradSq))
    (test_poincare hR hbound) u

lemma h10_norm_strain (hB : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H10Hilbert Ω, ‖u‖^2 ≤ C*jetStrainSq Ω u := by
  obtain ⟨R,hR,hbound⟩ := hB.exists_pos_norm_le
  have hb (x : X) (hx : x ∈ Ω) : |x 0| ≤ R := by
    have hn : |x 0| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    exact hn.trans (hbound x hx)
  refine ⟨2*(4*R^2+1),by positivity,?_⟩
  intro u
  have hp := h10_poincare hR hb u
  have hk := h10_korn u
  have he := jet_norm_sq u.val
  have hh : 0 ≤ 4*R^2+1 := by positivity
  have := mul_le_mul_of_nonneg_left hk hh
  change ‖u.val‖^2 ≤ _
  nlinarith

end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity

variable {Ω : Set X}

lemma SmoothUpTo.continuousOn_closure {a : X → ℝ} (ha : SmoothUpTo Ω a) :
    ContinuousOn a (closure Ω) := by
  obtain ⟨U,_,hs,hf⟩ := ha
  exact hf.continuousOn.mono hs

lemma SmoothUpTo.boundedCoefficient {a : X → ℝ} (ha : SmoothUpTo Ω a)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) : BoundedCoefficient Ω a := by
  have hc := ha.continuousOn_closure
  refine ⟨(hc.mono subset_closure).aestronglyMeasurable hO.measurableSet, ?_⟩
  obtain ⟨C,hC⟩ := hB.isCompact_closure.bddAbove_image hc.norm
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_ae_restrict hO.measurableSet] with x hx
  exact hC ⟨x,subset_closure hx,rfl⟩

lemma Admissible.uniform_positive {lam mu : X → ℝ} (ha : Admissible Ω lam mu)
    (hB : Bornology.IsBounded Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ closure Ω, c ≤ mu x ∧ c ≤ 3*lam x+2*mu x := by
  have hl := ha.1.continuousOn_closure
  have hm := ha.2.1.continuousOn_closure
  have hp : ContinuousOn (fun x => min (mu x) (3*lam x+2*mu x)) (closure Ω) :=
    hm.inf ((hl.const_mul 3).add (hm.const_mul 2))
  obtain ⟨c,hc,hbound⟩ := hB.isCompact_closure.exists_forall_le' hp
    (fun x hx => lt_min (ha.2.2 x hx).1 (ha.2.2 x hx).2)
  exact ⟨c,hc,fun x hx => le_min_iff.mp (hbound x hx)⟩

lemma trace_sq_le (A : Fin 3 → Fin 3 → ℝ) :
    (∑ i, A i i)^2 ≤ 3*∑ i, ∑ j, A i j^2 := by
  have ht : (∑ i, A i i)^2 ≤ 3*∑ i, A i i^2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => A i i))
  refine ht.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)

/-- Pointwise strong convexity controls the full physical symmetric strain,
including negative lambda. This uses the exact hypothesis 3λ+2μ>0. -/
lemma elasticity_density_lower (lam mu c : ℝ) (hc : 0 ≤ c) (hm : c ≤ mu)
    (hlm : c ≤ 3*lam+2*mu) (A : Fin 3 → Fin 3 → ℝ) :
    c*(∑ i, ∑ j, A i j^2) ≤ lam*(∑ i, A i i)^2+2*mu*(∑ i, ∑ j, A i j^2) := by
  have hA : 0 ≤ ∑ i, ∑ j, A i j^2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))
  by_cases hl : 0 ≤ lam
  · have h1 := mul_nonneg hl (sq_nonneg (∑ i, A i i))
    have h2 := mul_le_mul_of_nonneg_right hm hA
    have h3 := mul_nonneg (hc.trans hm) hA
    nlinarith
  · have ht := mul_le_mul_of_nonpos_left (trace_sq_le A) (le_of_not_ge hl)
    have hk := mul_le_mul_of_nonneg_right hlm hA
    nlinarith

lemma weighted_integrable {a : X → ℝ} (ha : BoundedCoefficient Ω a)
    (f g : ScalarL2 Ω) : Integrable (fun x => a x*f x*g x) (volume.restrict Ω) := by
  simpa only [Pi.mul_def] using (ha.mul_memLp f).integrable_mul (Lp.memLp g)

lemma jetEnergy_integral {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v : JetH Ω) :
    jetEnergy hl hm u v = ∫ x, lam x*jetDiv Ω u x*jetDiv Ω v x+
      2*mu x*∑ i, ∑ j, jetStrain Ω i j u x*jetStrain Ω i j v x ∂(volume.restrict Ω) := by
  have hL := weighted_integrable hl (jetDiv Ω u) (jetDiv Ω v)
  have hS (i j) := weighted_integrable hm (jetStrain Ω i j u) (jetStrain Ω i j v)
  rw [jetEnergy_apply,BoundedCoefficient.inner_mulL]
  simp_rw [BoundedCoefficient.inner_mulL]
  have hsum : Integrable (fun x => ∑ i, ∑ j,
      mu x*jetStrain Ω i j u x*jetStrain Ω i j v x) (volume.restrict Ω) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hS i j))
  calc
    _ = (∫ x, lam x*jetDiv Ω u x*jetDiv Ω v x ∂(volume.restrict Ω))+
        2*(∫ x, ∑ i, ∑ j, mu x*jetStrain Ω i j u x*jetStrain Ω i j v x
          ∂(volume.restrict Ω)) := by
      rw [integral_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun j _ => hS i j))]
      simp_rw [integral_finsetSum _ (fun j _ => hS _ j)]
    _ = ∫ x, lam x*jetDiv Ω u x*jetDiv Ω v x+
        2*(∑ i, ∑ j, mu x*jetStrain Ω i j u x*jetStrain Ω i j v x)
          ∂(volume.restrict Ω) := by
      rw [integral_add hL (hsum.const_mul 2),integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [Finset.mul_sum,mul_assoc])

lemma jetEnergy_eq_energy {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v : H1Hilbert Ω) :
    jetEnergy hl hm u v = energy Ω lam mu (h1Equiv Ω u) (h1Equiv Ω v) := by
  rw [jetEnergy_integral,energy]
  apply integral_congr_ae
  have hsu : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j,
      jetStrain Ω i j u.val x=((u.val (some j) x) i+(u.val (some i) x) j)/2 :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => jetStrain_ae u.val i j))
  have hsv : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j,
      jetStrain Ω i j v.val x=((v.val (some j) x) i+(v.val (some i) x) j)/2 :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => jetStrain_ae v.val i j))
  filter_upwards [jetDiv_ae u.val,jetDiv_ae v.val,hsu,hsv] with x hu hv hsu hsv
  simp only [hu,hv,hsu,hsv,div,strain,h1Equiv,Equiv.coe_fn_mk,jetEquiv_apply]

end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

lemma scalarL2_norm_sq (f : ScalarL2 Ω) :
    ‖f‖^2 = ∫ x, (f x)^2 ∂(volume.restrict Ω) := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

lemma scalarL2_integrable_sq (f : ScalarL2 Ω) :
    Integrable (fun x => (f x)^2) (volume.restrict Ω) := by
  simpa only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs] using
    L2.integrable_inner (𝕜 := ℝ) f f

lemma jetDiv_strain_ae (u : JetH Ω) :
    jetDiv Ω u =ᵐ[volume.restrict Ω] fun x => ∑ i, jetStrain Ω i i u x := by
  have hs : ∀ᵐ x ∂(volume.restrict Ω), ∀ i,
      jetStrain Ω i i u x=((u (some i) x) i+(u (some i) x) i)/2 :=
    Filter.eventually_all.mpr (fun i => jetStrain_ae u i i)
  filter_upwards [jetDiv_ae u,hs] with x hx hy
  rw [hx]
  apply Finset.sum_congr rfl
  intro i _
  rw [hy]
  ring

lemma jetStrainSq_integral (u : JetH Ω) :
    jetStrainSq Ω u = ∫ x, ∑ i, ∑ j, (jetStrain Ω i j u x)^2 ∂(volume.restrict Ω) := by
  unfold jetStrainSq
  simp_rw [scalarL2_norm_sq]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => scalarL2_integrable_sq _))]
  simp_rw [integral_finsetSum _ (fun j _ => scalarL2_integrable_sq _)]

lemma jetEnergy_lower (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (hO : IsOpen Ω) {c : ℝ} (hc : 0 ≤ c)
    (hp : ∀ x ∈ Ω, c ≤ mu x ∧ c ≤ 3*lam x+2*mu x) (u : JetH Ω) :
    c*jetStrainSq Ω u ≤ jetEnergy hl hm u u := by
  rw [jetStrainSq_integral,jetEnergy_integral,← integral_const_mul]
  have hS : Integrable (fun x => ∑ i, ∑ j, (jetStrain Ω i j u x)^2)
      (volume.restrict Ω) :=
    integrable_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => scalarL2_integrable_sq _))
  have hR : Integrable (fun x => lam x*jetDiv Ω u x*jetDiv Ω u x+
      2*mu x*∑ i, ∑ j, jetStrain Ω i j u x*jetStrain Ω i j u x)
      (volume.restrict Ω) := by
    have hsum := (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        weighted_integrable hm (jetStrain Ω i j u) (jetStrain Ω i j u)))).const_mul 2
    convert (weighted_integrable hl (jetDiv Ω u) (jetDiv Ω u)).add hsum using 1
    ext point
    simp only [Finset.mul_sum,mul_assoc,Pi.add_apply]
  apply integral_mono_ae (hS.const_mul c) hR
  filter_upwards [self_mem_ae_restrict hO.measurableSet,jetDiv_strain_ae u] with x hx hd
  have h := elasticity_density_lower (lam x) (mu x) c hc (hp x hx).1 (hp x hx).2
    (fun i j => jetStrain Ω i j u x)
  simpa only [hd,sq,mul_assoc] using h

/-- The actual Dirichlet physical energy on the exact zero-trace Hilbert space. -/
def zeroTraceEnergy (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu) :
    H10Hilbert Ω →L[ℝ] H10Hilbert Ω →L[ℝ] ℝ :=
  (jetEnergy hl hm).bilinearComp (H10Hilbert Ω).subtypeL (H10Hilbert Ω).subtypeL

lemma zeroTraceEnergy_apply (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u v : H10Hilbert Ω) : zeroTraceEnergy hl hm u v = jetEnergy hl hm u.val v.val := rfl

/-- Korn, supported Poincare and the exact strong convexity yield coercivity;
there is no sign restriction on lambda beyond 3 lambda + 2 mu > 0. -/
theorem physical_coercive (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) :
    IsCoercive (zeroTraceEnergy (ha.1.boundedCoefficient hO hB)
      (ha.2.1.boundedCoefficient hO hB)) := by
  obtain ⟨c,hc,hp⟩ := ha.uniform_positive hB
  obtain ⟨C,hC,hbound⟩ := h10_norm_strain hB
  refine ⟨c/C,div_pos hc hC,?_⟩
  intro u
  have hlower := jetEnergy_lower (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) hO hc.le (fun x hx => hp x (subset_closure hx)) u.val
  have hn := mul_le_mul_of_nonneg_left (hbound u) (div_pos hc hC).le
  rw [zeroTraceEnergy_apply]
  have he : c/C*C=c := div_mul_cancel₀ c (ne_of_gt hC)
  have hprod : c/C*‖u‖^2 ≤ c*jetStrainSq Ω u := by
    simpa only [← mul_assoc,he] using hn
  nlinarith

end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

def traceSetoid (Ω : Set X) : Setoid (H1 Ω) where
  r := SameTrace Ω
  iseqv := ⟨sameTrace_refl Ω,fun h => sameTrace_symm Ω h,fun h h' => sameTrace_trans Ω h h'⟩

lemma trace_eq_iff (u v : H1 Ω) : trace Ω u = trace Ω v ↔ SameTrace Ω u v := by
  exact ⟨fun h => Quotient.exact (s := traceSetoid Ω) h, Quot.sound⟩

lemma hasZeroTrace_h1Equiv (u : H1Hilbert Ω) :
    HasZeroTrace Ω (h1Equiv Ω u) ↔ u.val ∈ H10Hilbert Ω := Iff.rfl

lemma sameTrace_h1Equiv (u v : H1Hilbert Ω) :
    SameTrace Ω (h1Equiv Ω u) (h1Equiv Ω v) ↔ u.val-v.val ∈ H10Hilbert Ω := by
  change (jetEquiv Ω u.val-jetEquiv Ω v.val ∈ h10Submodule Ω) ↔
    jetEquiv Ω (u.val-v.val) ∈ h10Submodule Ω
  rw [map_sub]

lemma weakSolution_h1Equiv (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1Hilbert Ω) : WeakSolution Ω lam mu (h1Equiv Ω u) ↔
      ∀ v : H10Hilbert Ω, jetEnergy hl hm u.val v.val=0 := by
  constructor
  · intro h v
    let v' : H1Hilbert Ω := ⟨v.val,H10Hilbert_le Ω v.property⟩
    exact (jetEnergy_eq_energy hl hm u v').trans (h _ v.property)
  · intro h v hv
    let v' := (h1Equiv Ω).symm v
    have hz : v'.val ∈ H10Hilbert Ω := by
      rw [← hasZeroTrace_h1Equiv]
      simpa only [v',Equiv.apply_symm_apply] using hv
    have he := jetEnergy_eq_energy hl hm u v'
    simp only [v',Equiv.apply_symm_apply] at he
    rw [← he]
    exact h ⟨v'.val,hz⟩

/-- Lax--Milgram applied to the actual physical form and the exact jet
closures. The prescribed trace is arbitrary, not restricted to smooth data. -/
theorem dirichlet_exists (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (f : BoundaryData Ω) :
    ∃ u : H1 Ω, trace Ω u=f ∧ WeakSolution Ω lam mu u := by
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  let w := (h1Equiv Ω).symm f.out
  let L : H10Hilbert Ω →L[ℝ] ℝ := -(jetEnergy hl hm w.val).comp (H10Hilbert Ω).subtypeL
  let F := (InnerProductSpace.toDual ℝ (H10Hilbert Ω)).symm L
  have hC : IsCoercive (zeroTraceEnergy hl hm) := physical_coercive ha hO hB
  let z := hC.continuousLinearEquivOfBilin.symm F
  have hz (v : H10Hilbert Ω) : jetEnergy hl hm z.val v.val = -jetEnergy hl hm w.val v.val := by
    rw [← zeroTraceEnergy_apply,← hC.continuousLinearEquivOfBilin_apply]
    change inner ℝ (hC.continuousLinearEquivOfBilin (hC.continuousLinearEquivOfBilin.symm F)) v = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact InnerProductSpace.toDual_symm_apply
  let u : H1Hilbert Ω := ⟨w.val+z.val,
    (H1Hilbert Ω).add_mem w.property (H10Hilbert_le Ω z.property)⟩
  refine ⟨h1Equiv Ω u,?_,?_⟩
  · have ht : SameTrace Ω (h1Equiv Ω u) (h1Equiv Ω w) := by
      apply (sameTrace_h1Equiv u w).mpr
      change w.val+z.val-w.val ∈ H10Hilbert Ω
      simpa only [add_sub_cancel_left] using z.property
    calc
      trace Ω (h1Equiv Ω u) = trace Ω (h1Equiv Ω w) := Quot.sound ht
      _ = trace Ω f.out := by rw [Equiv.apply_symm_apply]
      _ = f := Quot.out_eq f
  · apply (weakSolution_h1Equiv hl hm u).mpr
    intro v
    change jetEnergy hl hm (w.val+z.val) v.val = 0
    rw [map_add,add_apply,hz]
    exact add_neg_cancel _

theorem dirichletSolution_spec (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (f : BoundaryData Ω) :
    trace Ω (dirichletSolution Ω lam mu f)=f ∧
      WeakSolution Ω lam mu (dirichletSolution Ω lam mu f) := by
  have hex := dirichlet_exists ha hO hB f
  simp only [dirichletSolution,dite_eq_left hex]
  exact Classical.choose_spec hex

theorem dirichlet_unique (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u v : H1 Ω)
    (hu : WeakSolution Ω lam mu u) (hv : WeakSolution Ω lam mu v)
    (ht : trace Ω u=trace Ω v) : u=v := by
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  let u' := (h1Equiv Ω).symm u
  let v' := (h1Equiv Ω).symm v
  have htu : SameTrace Ω (h1Equiv Ω u') (h1Equiv Ω v') := by
    simpa only [u',v',Equiv.apply_symm_apply] using (trace_eq_iff u v).mp ht
  let z : H10Hilbert Ω := ⟨u'.val-v'.val,(sameTrace_h1Equiv u' v').mp htu⟩
  have hu' : ∀ w : H10Hilbert Ω, jetEnergy hl hm u'.val w.val=0 :=
    (weakSolution_h1Equiv hl hm u').mp (by simpa only [u',Equiv.apply_symm_apply] using hu)
  have hv' : ∀ w : H10Hilbert Ω, jetEnergy hl hm v'.val w.val=0 :=
    (weakSolution_h1Equiv hl hm v').mp (by simpa only [v',Equiv.apply_symm_apply] using hv)
  have hz : zeroTraceEnergy hl hm z z=0 := by
    change jetEnergy hl hm (u'.val-v'.val) z.val=0
    rw [map_sub (jetEnergy hl hm) u'.val v'.val,sub_apply,hu',hv',sub_self]
  obtain ⟨c,hc,hbound⟩ := physical_coercive ha hO hB
  have hn : ‖z‖=0 := by
    have hh := hbound z
    rw [hz] at hh
    have hs : ‖z‖*‖z‖ ≤ 0 := (mul_le_mul_iff_right₀ hc).mp (by nlinarith only [hh])
    nlinarith [norm_nonneg z]
  have he : u'=v' := by
    apply Subtype.ext
    have hval := congrArg Subtype.val (norm_eq_zero.mp hn)
    change u'.val-v'.val=0 at hval
    exact sub_eq_zero.mp hval
  exact (h1Equiv Ω).symm.injective he

end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

lemma jetEnergy_symm (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u v : JetH Ω) : jetEnergy hl hm u v=jetEnergy hl hm v u := by
  rw [jetEnergy_integral,jetEnergy_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    have hs : (∑ i, ∑ j, jetStrain Ω i j u x*jetStrain Ω i j v x)=
        ∑ i, ∑ j, jetStrain Ω i j v x*jetStrain Ω i j u x := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    dsimp only
    rw [hs]
    ring)

lemma energy_symm (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u v : H1 Ω) : energy Ω lam mu u v=energy Ω lam mu v u := by
  have h := jetEnergy_symm hl hm ((h1Equiv Ω).symm u).val ((h1Equiv Ω).symm v).val
  rwa [jetEnergy_eq_energy,jetEnergy_eq_energy,Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at h

lemma energy_eq_of_sameTrace (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    {u v w : H1 Ω} (hu : WeakSolution Ω lam mu u) (hvw : SameTrace Ω v w) :
    energy Ω lam mu u v=energy Ω lam mu u w := by
  let u' := (h1Equiv Ω).symm u
  let v' := (h1Equiv Ω).symm v
  let w' := (h1Equiv Ω).symm w
  have ht : v'.val-w'.val ∈ H10Hilbert Ω :=
    (sameTrace_h1Equiv v' w').mp (by simpa only [v',w',Equiv.apply_symm_apply] using hvw)
  have he := (weakSolution_h1Equiv hl hm u').mp (by
    simpa only [u',Equiv.apply_symm_apply] using hu) ⟨v'.val-w'.val,ht⟩
  change jetEnergy hl hm u'.val (v'.val-w'.val)=0 at he
  rw [map_sub] at he
  have hv' := jetEnergy_eq_energy hl hm u' v'
  have hw' := jetEnergy_eq_energy hl hm u' w'
  simp only [u',v',w',Equiv.apply_symm_apply] at hv' hw'
  rw [hv',hw'] at he
  exact sub_eq_zero.mp he

lemma DN_eq_energy (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (f : BoundaryData Ω) (v : H1 Ω) :
    DN Ω lam mu f (trace Ω v)=energy Ω lam mu (dirichletSolution Ω lam mu f) v := by
  apply energy_eq_of_sameTrace (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) (dirichletSolution_spec ha hO hB f).2
  apply (trace_eq_iff _ _).mp
  exact Quot.out_eq (trace Ω v)

lemma solution_eq_dirichlet (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) {u : H1 Ω} (hu : WeakSolution Ω lam mu u) :
    u=dirichletSolution Ω lam mu (trace Ω u) :=
  dirichlet_unique ha hO hB _ _ hu (dirichletSolution_spec ha hO hB _).2
    (dirichletSolution_spec ha hO hB _).1.symm

theorem interior_physical_transfer {lam₁ mu₁ lam₂ mu₂ : X → ℝ}
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
    {u₁ : H1 Ω} (hu₁ : WeakSolution Ω lam₁ mu₁ u₁) :
    ∃ u₂ : H1 Ω, WeakSolution Ω lam₂ mu₂ u₂ ∧ trace Ω u₂=trace Ω u₁ ∧
      ∀ v : H1 Ω, energy Ω lam₂ mu₂ u₂ v=energy Ω lam₁ mu₁ u₁ v := by
  let u₂ := dirichletSolution Ω lam₂ mu₂ (trace Ω u₁)
  have hs := dirichletSolution_spec ha₂ hO hB (trace Ω u₁)
  refine ⟨u₂,hs.2,hs.1,?_⟩
  intro v
  rw [← DN_eq_energy ha₂ hO hB,← hDN,DN_eq_energy ha₁ hO hB]
  rw [← solution_eq_dirichlet ha₁ hO hB hu₁]

end Elasticity

end
end

end OAI
