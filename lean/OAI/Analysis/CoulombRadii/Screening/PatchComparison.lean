import Mathlib
import OAI.Analysis.CoulombRadii.Screening.FineCountTest
import OAI.Analysis.CoulombRadii.ThomasFermi.PatchGeometry

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap
noncomputable section
namespace Coulomb

lemma weighted_cap_count_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w F N : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hF : AEStronglyMeasurable F μ) (hF0 : ∀ᵐ x ∂μ, 0≤F x)
    (hFi : Integrable (fun x => w x*(F x)^2) μ)
    (hN : AEStronglyMeasurable N μ) {n : ℝ} (hn : 0≤n)
    (hN0 : ∀ᵐ x ∂μ, 0≤N x ∧ N x≤n) :
    Integrable (fun x => w x*(F x*N x)) μ := by
  apply ((hw.add hFi).const_mul n).mono' (hw.aestronglyMeasurable.mul (hF.mul hN))
  filter_upwards [hw0,hF0,hN0] with x hw hf hnn
  dsimp only [Pi.add_apply,Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg hw (mul_nonneg hf hnn.1))]
  have h1 := mul_le_mul_of_nonneg_left hnn.2 (mul_nonneg hw hf)
  have h2 := mul_nonneg (mul_nonneg hw hn) (sq_nonneg (F x-1/2))
  nlinarith

lemma patch_diameter {a b t : ℝ} (_ : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space) :
    ∀ x∈Metric.ball y (t-4*b), ∀ z∈Metric.ball y (t-4*b), ‖x-z‖≤12*a := by
  intro x hx z hz
  have hx' : ‖x-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hz' : ‖z-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have hh := norm_sub_le_norm_sub_add_norm_sub x y z
  rw [norm_sub_rev y z] at hh
  linarith

lemma patch_retained_separated {n : ℕ} {a b t : ℝ} (_ : 0<a) (hb : 0<b)
    (y : Space) (x : Configuration n) :
    ∀ z∈{z | t≤‖z-y‖}, ∀ i∈patchRetained y t b x, Real.sqrt 3*b≤‖z-position x i‖ := by
  intro z hz i hi
  have hsmall : Real.sqrt 3≤2 := by exact (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have hret := (patchRetained_mem ..).mp hi
  have H := norm_sub_le_norm_sub_add_norm_sub z (position x i) y
  change t≤‖z-y‖ at hz
  nlinarith

theorem physical_patch_comparison {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k))
    (ho : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ):ℂ)*ψ.value (outerAppend s t) z)
    (hc : ∀ s, ∀ᵐ x, Antisymmetric (ψ.coreSlice s x))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t∈Set.Icc (5*a) (6*a))
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized {z | t≤‖z-y‖})
    (hos : ∀ s, ∀ᵐ x, mass (ψ.coreSlice s x)≠0 → ∀ i, position x i∈Metric.closedBall y (t+b))
    (F : Spins m → Configuration m → ℝ)
    (hFm : ∀ s, AEStronglyMeasurable (F s) volume)
    (hF0 : ∀ s, ∀ᵐ x, 0≤F s x)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x)^2))
    (hcap : ∀ s, ∀ᵐ x, ∀ w∈Metric.closedBall y (t+b), coreScreenedField S (ψ.coreSlice s x).normalized w≤F s x)
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) :
    let ρ := fun s x => localTFDensity measurableSet_ball
      (coreTFField S (ψ.coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht.2 y hn))
    sliceExpectation ψ (fun s x => rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
      (retainedFineDensity b (patchRetained y t b x) (position x))-
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)) ≤
      form S ψ-E*mass ψ+
      sliceExpectation ψ (fun s x => packetKineticError (scaledWindow unitWindow b hb.ne') (ρ s x))+
      sliceExpectation ψ (fun s x => F s x*localCount {z | t-7*b≤‖z-y‖} x)+fineLocalizationError m b*mass ψ := by
  dsimp only
  let ρ := fun s x => localTFDensity measurableSet_ball
    (coreTFField S (ψ.coreSlice s x).normalized measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn))
  have hcap' (s : Spins m) : ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S (ψ.coreSlice s x).normalized w≤F s x := by
    filter_upwards [hcap s] with x hx
    intro w hw
    apply hx w
    exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw
  have hTF (s : Spins m) := coreTF_conditional_integrable measurableSet_ball S ψ s ha
    (patch_nucleus_separation S ha hb ht.2 y hn) (show 0<12*a by positivity)
    (patch_diameter ha hb ht.2 y) (F s) (hF0 s) (hFi s) (hcap' s)
  have hFC (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(F s x*(deletedLabels (patchRetained y t b) x).card)) := by
    simp_rw [deletedLabels_patchRetained]
    exact weighted_cap_count_integrable (mass_coreSlice_integrable ψ s)
      (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm s) (hF0 s) (hFi s)
      (localCount_measurable (isClosed_le continuous_const (by fun_prop)).measurableSet).aestronglyMeasurable
      (Nat.cast_nonneg m) (Eventually.of_forall (fun x => ⟨localCount_nonneg _ x,localCount_le _ x⟩))
  have hKC (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*packetKineticError (scaledWindow unitWindow b hb.ne') (ρ s x)) := by
    unfold packetKineticError
    convert (hTF s).1.mul_const ((1/2:ℝ)*(∑ j : Fin 3, ∫ z : Space,
      (fderiv ℝ (scaledWindow unitWindow b hb.ne') z (EuclideanSpace.single j 1))^2)) using 1
    funext x
    ring
  let F' := fun s x => if mass (ψ.coreSlice s x)=0 then
    ∑ i : Fin m, max (coreScreenedField S (ψ.coreSlice s x).normalized (position x i)) 0 else F s x
  have hFC' (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(F' s x*(deletedLabels (patchRetained y t b) x).card)) := by
    apply (hFC s).congr
    filter_upwards [] with x
    dsimp only [F']
    split_ifs with hm <;> simp_all
  have hFE : sliceExpectation ψ (fun s x => F' s x*(deletedLabels (patchRetained y t b) x).card)=
      sliceExpectation ψ (fun s x => F s x*localCount {z | t-7*b≤‖z-y‖} x) := by
    apply Finset.sum_congr rfl
    intro s hs
    apply integral_congr_ae
    filter_upwards [] with x
    rw [deletedLabels_patchRetained]
    dsimp only [F']
    split_ifs with hm <;> simp_all
  have HH := source_free_patch_comparison S ψ ho hc hb (patchRetained y t b) (patchRetained_measurable y t b)
    F' hFC' (show ∀ s, ∀ᵐ x, ∀ i∈deletedLabels (patchRetained y t b) x,
      coreScreenedField S (ψ.coreSlice s x).normalized (position x i)≤F' s x from ?_)
    (scaledWindow unitWindow b hb.ne') (by rw [scaledWindow_mass _ hb,unitWindow_mass])
    (scaledWindow_compactSupport unitWindow unitWindow_support hb)
    (scaledWindow_radial unitWindow unitWindow_radial hb) hb
    (scaledWindow_support unitWindow unitWindow_support hb) ρ
    (fun _ _ => Metric.closedBall y (t-4*b)) (fun _ _ => {z | t≤‖z-y‖})
    (show ∀ s, ∀ᵐ x, SourceFreeHoleDensity S (ψ.coreSlice s x).normalized _ b (ρ s x) _ _ from ?_)
    (show ∀ s : Spins m, ∀ᵐ x, ∀ j i, i∈patchRetained y t b x → Real.sqrt 3*b≤‖S.position j-position x i‖ from ?_)
    (fun _ => Eventually.of_forall (fun x => patch_retained_separated ha hb y x))
    (fun s => (hTF s).2) hKC hE
  · rwa [hFE] at HH
  · intro s
    filter_upwards [hcap s,hos s] with x hx ho
    intro i hi
    dsimp only [F']
    split_ifs with hm
    · exact (le_max_left _ 0).trans (Finset.single_le_sum (fun j _ => le_max_right (coreScreenedField S (ψ.coreSlice s x).normalized (position x j)) 0) (Finset.mem_univ i))
    · exact hx _ (ho hm i)
  · intro s
    filter_upwards [hcs s] with x hx
    exact patch_hole_density S _ ha hb hsmall ht.2 y hx hn _
  · intro s
    filter_upwards [] with x
    intro j i hi
    have hret := (patchRetained_mem ..).mp hi
    have H := norm_sub_le_norm_sub_add_norm_sub (S.position j) (position x i) y
    have hs : Real.sqrt 3≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
    nlinarith [hn j,ht.2]

end Coulomb
end

end
end

end OAI
