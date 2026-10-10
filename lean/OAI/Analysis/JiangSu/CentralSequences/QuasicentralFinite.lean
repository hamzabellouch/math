import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.QuasicentralResolvent

namespace OAI

noncomputable section
namespace Quasicentral

section
open Filter Topology Pureness
open scoped ComplexOrder NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_strict_ideal_contraction (J : ClosedStarIdeal A) (W : Finset A)
    (hW : ∀ w∈W, w∈J.ideal) {ε : ℝ} (hε : 0<ε) :
    ∃ e : A, e∈J.ideal ∧ 0≤e ∧ ‖e‖<1 ∧
      ∀ w∈W, ‖star w*(1-e)*w‖<ε^2 := by
  let l := CStarAlgebra.approximateUnit J.idealStarAlgebra
  have hl := CStarAlgebra.increasingApproximateUnit J.idealStarAlgebra
  have hw (w : A) (hw : w∈W) :
      ∀ᶠ e : J.idealStarAlgebra in l, ‖star w*(1-(e:A))*w‖<ε^2 := by
    let w' : J.idealStarAlgebra := ⟨w,hW w hw⟩
    have ht := (tendsto_const_nhds (x := w')).sub (hl.tendsto_mul_right w')
    have ht' := (tendsto_const_nhds (x := star w')).mul ht
    have hn := (continuous_norm.tendsto (0 : J.idealStarAlgebra)).comp (by simpa using ht')
    simp only [norm_zero] at hn
    have hn' := hn.eventually (gt_mem_nhds (sq_pos_of_pos hε))
    filter_upwards [hn'] with e he
    change ‖star w*(w-(e:A)*w)‖<ε^2 at he
    simpa only [mul_sub,sub_mul,mul_one,mul_assoc] using he
  have hall : ∀ᶠ e : J.idealStarAlgebra in l, ∀ w∈W, ‖star w*(1-(e:A))*w‖<ε^2 :=
    (eventually_all_finset W).mpr hw
  obtain ⟨e,⟨hp,hn⟩,he⟩ :=
    (CStarAlgebra.hasBasis_approximateUnit J.idealStarAlgebra).eventually_iff.mp hall
  refine ⟨e,e.2,J.idealInclusion_nonneg hp,hn,?_⟩
  exact he ⟨@le_refl _ J.idealPartialOrder.toPreorder e,by simpa only [Metric.mem_closedBall,dist_zero_right] using hn.le⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma ideal_conjugate_mem (J : ClosedStarIdeal A) (u : unitary A) {a : A}
    (ha : a∈J.ideal) : conjugate u a∈J.ideal :=
  J.ideal.mul_mem_right _ _ (J.ideal.mul_mem_left _ _ ha)

theorem exists_quasicentral_unitary_contraction (J : ClosedStarIdeal A)
    (K : Finset (unitary A)) (hKstar : ∀ u∈K, star u∈K)
    (W : Finset A) (hW : ∀ w∈W, w∈J.ideal) {ε : ℝ} (hε : 0<ε)
    {N : ℕ} (hN : 0<N) :
    ∃ e : A, e∈J.ideal ∧ 0≤e ∧ e≤1 ∧
      (∀ w∈W, ‖w-e*w‖≤ε) ∧
      (∀ u∈K, ‖(u:A)*e-e*(u:A)‖≤(N:ℝ)⁻¹) := by
  obtain ⟨e₀,he₀J,he₀,he₀n,he₀W⟩ := exists_strict_ideal_contraction J W hW hε
  obtain ⟨e,heJ,hep,he1,he₀e,heK⟩ := exists_logarithmic_contraction
    J.idealStarAlgebra J.isClosed K hKstar (fun u _ a ha => ideal_conjugate_mem J u ha)
    he₀J he₀ he₀n hN
  refine ⟨e,heJ,hep,he1,?_,heK⟩
  intro w hw
  exact CStarAlgebra.norm_sub_mul_self_le w he₀ ⟨he₀e,he1⟩ hε.le (he₀W w hw).le

theorem exists_quasicentral_contraction (J : ClosedStarIdeal A) (F W : Finset A)
    (hW : ∀ w∈W, w∈J.ideal) {ε : ℝ} (hε : 0<ε) :
    ∃ e : A, e∈J.ideal ∧ 0≤e ∧ e≤1 ∧
      (∀ w∈W, ‖w-e*w‖≤ε) ∧ (∀ a∈F, ‖a*e-e*a‖<ε) := by
  classical
  choose u c huc hc using (fun a : A => CStarAlgebra.exists_sum_four_unitary a)
  let K₀ : Finset (unitary A) := F.biUnion (fun a => Finset.univ.image (u a))
  let K := K₀ ∪ K₀.image star
  have huK (a : A) (ha : a∈F) (i : Fin 4) : u a i∈K :=
    Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  have hKs (v : unitary A) (hv : v∈K) : star v∈K := by
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_union_left _ (by simpa using hw)
  let M : ℝ := 1+∑ a∈F, 2*‖a‖
  have hM : 0<M := lt_add_of_pos_of_le zero_lt_one (Finset.sum_nonneg fun a _ => by positivity)
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (div_pos hε hM)
  have hn' : ((n+1:ℕ):ℝ)⁻¹ < ε/M := by simpa only [Nat.cast_add,Nat.cast_one,one_div] using hn
  obtain ⟨e,heJ,hep,he1,heW,heK⟩ := exists_quasicentral_unitary_contraction J K hKs W hW hε (Nat.succ_pos n)
  refine ⟨e,heJ,hep,he1,heW,?_⟩
  intro a ha
  have hMa : 2*‖a‖ ≤ M :=
    (Finset.single_le_sum (f := fun b : A => 2*‖b‖) (fun b _ => by positivity) ha).trans (le_add_of_nonneg_left zero_le_one)
  calc
    ‖a*e-e*a‖ = ‖∑ i : Fin 4, c a i • ((u a i:A)*e-e*(u a i:A))‖ := by
      congr 1
      conv_lhs => rw [huc a]
      simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin 4, ‖c a i‖*‖(u a i:A)*e-e*(u a i:A)‖ := by
      simpa only [norm_smul] using norm_sum_le Finset.univ (fun i : Fin 4 => c a i • ((u a i:A)*e-e*(u a i:A)))
    _ ≤ ∑ _i : Fin 4, (‖a‖/2)*((n+1:ℕ):ℝ)⁻¹ :=
      Finset.sum_le_sum fun i _ => mul_le_mul (hc a i) (heK _ (huK a ha i)) (norm_nonneg _) (by positivity)
    _ = 2*‖a‖*((n+1:ℕ):ℝ)⁻¹ := by simp; ring
    _ ≤ M*((n+1:ℕ):ℝ)⁻¹ := mul_le_mul_of_nonneg_right hMa (by positivity)
    _ < M*(ε/M) := mul_lt_mul_of_pos_left hn' hM
    _ = ε := mul_div_cancel₀ ε hM.ne'

end

open Filter Topology Pureness
open scoped ComplexOrder NNReal

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A]

def unitizedKernel (φ : A →⋆ₙₐ[ℂ] B) : ClosedStarIdeal (Unitization ℂ A) where
  ideal := TwoSidedIdeal.ker (Unitization.starMap φ)
  star_mem := by
    intro x hx
    rw [TwoSidedIdeal.mem_ker] at hx ⊢
    rw [map_star,hx,star_zero]
  isClosed := by
    convert isClosed_singleton.preimage (show Continuous (Unitization.starMap φ) by fun_prop) using 1
    ext x
    exact TwoSidedIdeal.mem_ker _

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizedKernel_mem {φ : A →⋆ₙₐ[ℂ] B} {x : Unitization ℂ A}
    (hx : x∈(unitizedKernel φ).ideal) : x.fst=0 ∧ φ x.snd=0 := by
  have hx := (TwoSidedIdeal.mem_ker (Unitization.starMap φ)).mp hx
  have hf := congrArg (fun y : Unitization ℂ B => y.fst) hx
  have hs := congrArg (fun y : Unitization ℂ B => y.snd) hx
  simpa [Unitization.starMap_apply,Unitization.algebraMap_eq_inl] using And.intro hf hs

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_mem_unitizedKernel {φ : A →⋆ₙₐ[ℂ] B} {x : A} (hx : φ x=0) :
    Unitization.inr x∈(unitizedKernel φ).ideal := by
  apply (TwoSidedIdeal.mem_ker (Unitization.starMap φ)).mpr
  simp [hx]

theorem exists_quasicentral_kernel_contraction (φ : A →⋆ₙₐ[ℂ] B)
    (F W : Finset A) (hW : ∀ w∈W, φ w=0) {ε : ℝ} (hε : 0<ε) :
    ∃ e : A, φ e=0 ∧ 0≤e ∧ ‖e‖≤1 ∧
      (∀ w∈W, ‖w-e*w‖≤ε) ∧ (∀ a∈F, ‖a*e-e*a‖<ε) := by
  classical
  let J := unitizedKernel φ
  let i : A → Unitization ℂ A := Unitization.inr
  obtain ⟨e,heJ,hep,he1,heW,heF⟩ := exists_quasicentral_contraction J (F.image i) (W.image i)
    (by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨v,hv,hvw⟩
      subst w
      exact inr_mem_unitizedKernel (hW v hv)) hε
  obtain ⟨hef,heφ⟩ := unitizedKernel_mem heJ
  have hei : Unitization.inr e.snd=e := by
    have h := Unitization.inl_fst_add_inr_snd_eq e
    simpa only [hef,Unitization.inl_zero,zero_add] using h
  refine ⟨e.snd,heφ,?_,?_,?_,?_⟩
  · exact Unitization.inr_nonneg_iff.mp (hei.symm ▸ hep)
  · have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hep).mpr he1
    rwa [← hei,Unitization.norm_inr] at hn
  · intro w hw
    have h := heW (i w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    rw [← hei] at h
    simpa only [i,← Unitization.inr_mul,← Unitization.inr_sub,Unitization.norm_inr] using h
  · intro a ha
    have h := heF (i a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    rw [← hei] at h
    simpa only [i,← Unitization.inr_mul,← Unitization.inr_sub,Unitization.norm_inr] using h

end Quasicentral
end

end OAI
