import OAI.Analysis.CharacterCriterion.MultiplicativeChannels

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.BalancedDropChannels
open MatrixDiagonalPath DiagonalIteration BalancedDropIteration
open BalancedDropMultiplicity BalancedDropSystem DropChannels
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology

def finalPath (n k : ℕ) := normalizedPath n (k+1)
def endPath (n k : ℕ) (t : unitInterval) := finalPath n k t*star (finalPath n k 1)
lemma endPath_continuous (n k : ℕ) : Continuous (endPath n k) :=
  (normalizedPath_continuous n (k+1)).mul continuous_const
@[simp] lemma endPath_one (n k : ℕ) : endPath n k 1=1 := mul_inv_cancel _
def stageLeft (n k : ℕ) : Channel DimensionDrop23 (BalancedDropLimit.Stage (n+k+1)) :=
  DropChannels.left (next (stage (n+k))) (next (stage (n+k))+1)
    (finalPath n k) (normalizedPath_continuous n (k+1)) (normalizedPath_zero n (k+1))
    (zeroRep (stage (n+k)) (stage_two (n+k)) (normalizedPath n k half))
def stageRight (n k : ℕ) : Channel DimensionDrop23 (BalancedDropLimit.Stage (n+k+1)) :=
  DropChannels.right (next (stage (n+k))) (next (stage (n+k))+1)
    (endPath n k) (endPath_continuous n k) (endPath_one n k)
    (oneRep (stage (n+k)) (stage_two (n+k))
      (normalizedPath n k half*star (normalizedPath n k 1)))
lemma stage_unit_sum (n k : ℕ) : stageLeft n k 1+stageRight n k 1=1 :=
  DropChannels.unit_sum _ _ _ _ _ _ _ _ _ _
lemma norm_sub_two {B : Type*} [SeminormedAddCommGroup B] (a b c : B) {ε : ℝ}
    (ha : ‖a-c‖≤ε) (hb : ‖b-c‖≤ε) : ‖a-b‖≤2*ε := by
  calc
    _ = ‖(a-c)-(b-c)‖ := by congr 1; abel
    _ ≤ ‖a-c‖+‖b-c‖ := norm_sub_le _ _
    _ ≤ _ := by linarith
lemma map_next (n k : ℕ) (x : BalancedDropLimit.Stage n) :
    BalancedDropLimit.chain.map n (n+k+1) (by omega) x =
      step (stage (n+k)) (stage_two (n+k))
        (BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) x) := by
  rw [BalancedDropLimit.chain.map_succ n (n+k) (Nat.le_add_right n k)]
  rfl
lemma stageLeft_bound (n k : ℕ) (x : BalancedDropLimit.Stage n) {ε : ℝ} (hε : 0≤ε)
    (hp : ∀ t : unitInterval,
      ‖conj (star (normalizedPath n k t))
        ((BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε)
    (hf : ∀ t : unitInterval,
      ‖conj (star (finalPath n k t))
        ((BalancedDropLimit.chain.map n (n+k+1) (by omega) x).val t)-
        (BalancedDropLimit.chain.map n (n+k+1) (by omega) x).val 0‖≤ε)
    (d : DimensionDrop23) :
    ‖stageLeft n k d * (show BalancedDropLimit.Stage (n+k+1) from BalancedDropLimit.chain.map n (n+k+1) (by omega) x)-
      (show BalancedDropLimit.Stage (n+k+1) from BalancedDropLimit.chain.map n (n+k+1) (by omega) x) * stageLeft n k d‖≤4*ε*‖d‖ := by
  let g : BalancedDropLimit.Stage (n+k+1) := BalancedDropLimit.chain.map n (n+k+1) (by omega) x
  change ‖((stageLeft n k d*g-g*stageLeft n k d).val)‖≤_
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖(leftScalar t • conj (finalPath n k t)
      (MatrixTensor.leftMatrix (zeroRep (stage (n+k)) (stage_two (n+k)) (normalizedPath n k half) d))) * g.val t-
    g.val t*(leftScalar t • conj (finalPath n k t)
      (MatrixTensor.leftMatrix (zeroRep (stage (n+k)) (stage_two (n+k)) (normalizedPath n k half) d)))‖≤_
  apply (smul_commutator _ _ _ (leftScalar_norm t)).trans
  let ρ : DimensionDrop23 →⋆ₐ[ℂ] MatrixTensor.Mat (P (next (stage (n+k))) × Q (next (stage (n+k)))) := MatrixTensor.leftMatrix.comp
    (zeroRep (stage (n+k)) (stage_two (n+k)) (normalizedPath n k half))
  have he := zeroRep_bound (stage (n+k)) (stage_two (n+k)) (normalizedPath n k half)
    (BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) x) d (hp half)
  rw [←map_next n k x] at he
  have ht := transport_bound ρ d (finalPath n k t) (g.val t) (g.val 0) hε (hf t) he
  convert ht using 1 <;> first | rfl | ring
lemma stageRight_bound (n k : ℕ) (x : BalancedDropLimit.Stage n) {ε : ℝ} (hε : 0≤ε)
    (hp : ∀ t : unitInterval,
      ‖conj (star (normalizedPath n k t))
        ((BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε)
    (hf : ∀ t : unitInterval,
      ‖conj (star (finalPath n k t))
        ((BalancedDropLimit.chain.map n (n+k+1) (by omega) x).val t)-
        (BalancedDropLimit.chain.map n (n+k+1) (by omega) x).val 0‖≤ε)
    (d : DimensionDrop23) :
    ‖stageRight n k d * (show BalancedDropLimit.Stage (n+k+1) from BalancedDropLimit.chain.map n (n+k+1) (by omega) x)-
      (show BalancedDropLimit.Stage (n+k+1) from BalancedDropLimit.chain.map n (n+k+1) (by omega) x) * stageRight n k d‖≤8*ε*‖d‖ := by
  let f : BalancedDropLimit.Stage (n+k) := BalancedDropLimit.chain.map n (n+k) (Nat.le_add_right n k) x
  let g : BalancedDropLimit.Stage (n+k+1) := BalancedDropLimit.chain.map n (n+k+1) (by omega) x
  have hm : ‖conj (star (normalizedPath n k half*star (normalizedPath n k 1)))
      (f.val half)-f.val 1‖≤2*ε := by
    rw [norm_twisted_difference]
    exact norm_sub_two _ _ _ (hp half) (hp 1)
  have he := oneRep_bound (stage (n+k)) (stage_two (n+k))
    (normalizedPath n k half*star (normalizedPath n k 1)) f d hm
  change _ ≤ 2*(2*ε)*‖d‖ at he
  rw [show 2*(2*ε)*‖d‖=(4*ε)*‖d‖ by ring] at he
  dsimp only [f] at he
  rw [←map_next n k x] at he
  change ‖((stageRight n k d*g-g*stageRight n k d).val)‖≤_
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖(rightScalar t • conj (endPath n k t)
      (MatrixTensor.rightMatrix (oneRep (stage (n+k)) (stage_two (n+k))
        (normalizedPath n k half*star (normalizedPath n k 1)) d))) * g.val t-
    g.val t*(rightScalar t • conj (endPath n k t)
      (MatrixTensor.rightMatrix (oneRep (stage (n+k)) (stage_two (n+k))
        (normalizedPath n k half*star (normalizedPath n k 1)) d)))‖≤_
  apply (smul_commutator _ _ _ (rightScalar_norm t)).trans
  let ρ : DimensionDrop23 →⋆ₐ[ℂ] MatrixTensor.Mat (P (next (stage (n+k))) × Q (next (stage (n+k)))) := MatrixTensor.rightMatrix.comp (oneRep (stage (n+k)) (stage_two (n+k))
    (normalizedPath n k half*star (normalizedPath n k 1)))
  have ht : ‖conj (star (endPath n k t)) (g.val t)-g.val 1‖≤2*ε := by
    rw [endPath,norm_twisted_difference]
    exact norm_sub_two _ _ _ (hf t) (hf 1)
  have hc := transport_bound ρ d (endPath n k t) (g.val t) (g.val 1) (by positivity : 0≤2*ε) ht he
  convert hc using 1 <;> first | rfl | ring
end KirchbergRordam.BalancedDropChannels
namespace KirchbergRordam.BalancedDropChannels
open BalancedDropLimit BalancedDropIteration
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology
lemma finite_stage (n : ℕ) (F : Finset (Stage n)) (ε : ℝ) (hε : 0<ε) :
    ∃ φ ψ : Channel DimensionDrop23 Algebra, φ 1+ψ 1=1 ∧
      ∀ x∈F, ∀ d : DimensionDrop23,
        ‖φ d*inclusion n x-inclusion n x*φ d‖≤ε*‖d‖ ∧
        ‖ψ d*inclusion n x-inclusion n x*ψ d‖≤ε*‖d‖ := by
  have he : ∀ᶠ k in atTop, ∀ x∈F, ∀ t : unitInterval,
      ‖DiagonalIteration.conj (star (normalizedPath n k t))
        ((chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε/8 := by
    apply (Filter.eventually_all_finset F).mpr
    intro x hx
    exact eventually_untwist_small n x (ε/8) (by positivity)
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp he
  let φ := MultiplicativeChannel.postcompose (stageLeft n K) (inclusion (n+K+1))
  let ψ := MultiplicativeChannel.postcompose (stageRight n K) (inclusion (n+K+1))
  refine ⟨φ,ψ,?_,fun x hx d => ?_⟩
  · change BalancedDropLimit.inclusion _ (stageLeft n K 1)+BalancedDropLimit.inclusion _ (stageRight n K 1)=1
    rw [←map_add,stage_unit_sum,map_one]
  · have hl := stageLeft_bound n K x (by positivity : 0≤ε/8) (hK K le_rfl x hx)
      (hK (K+1) (Nat.le_succ K) x hx) d
    have hr := stageRight_bound n K x (by positivity : 0≤ε/8) (hK K le_rfl x hx)
      (hK (K+1) (Nat.le_succ K) x hx) d
    have hm : inclusion (n+K+1) (chain.map n (n+K+1) (by omega) x)=inclusion n x :=
      CStarInductiveLimit.of_map system n (n+K+1) (by omega) x
    have hc (r : Stage (n+K+1)) := DropChannels.commutator_map_bound
      (inclusion (n+K+1)) r (chain.map n (n+K+1) (by omega) x)
    have hcl := (hc (stageLeft n K d)).trans hl
    have hcr := (hc (stageRight n K d)).trans hr
    rw [hm] at hcl hcr
    change _≤_ at hcl
    refine ⟨hcl.trans ?_,hcr.trans ?_⟩ <;> nlinarith [norm_nonneg d]

lemma channel_perturbation (φ : Channel DimensionDrop23 Algebra) (d : DimensionDrop23)
    (x y : Algebra) :
    ‖φ d*x-x*φ d‖≤‖φ d*y-y*φ d‖+2*‖x-y‖*‖d‖ := by
  calc
    _ ≤ ‖φ d*y-y*φ d‖+2*‖x-y‖*‖φ d‖ := DropChannels.norm_commutator_change (φ d) x y
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (φ.norm_le d)
      (by positivity : 0≤2*‖x-y‖))

lemma finite_control (F : Finset Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ φ ψ : Channel DimensionDrop23 Algebra, φ 1+ψ 1=1 ∧
      ∀ x∈F, ∀ d : DimensionDrop23,
        ‖φ d*x-x*φ d‖≤ε*‖d‖ ∧ ‖ψ d*x-x*ψ d‖≤ε*‖d‖ := by
  classical
  obtain ⟨n,a,ha⟩ := BalancedDropHalfFlip.common_stage F (ε/4) (by positivity)
  obtain ⟨φ,ψ,hu,h⟩ := finite_stage n (F.image a) (ε/2) (by positivity)
  refine ⟨φ,ψ,hu,fun x hx d => ?_⟩
  have hb := h (a x) (Finset.mem_image_of_mem a hx) d
  have hd := (ha x hx).le
  rw [norm_sub_rev] at hd
  constructor
  · have hc := channel_perturbation φ d x (inclusion n (a x))
    nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg d),hb.1]
  · have hc := channel_perturbation ψ d x (inclusion n (a x))
    nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg d),hb.2]
end KirchbergRordam.BalancedDropChannels
namespace KirchbergRordam.MultiplicativeChannel
open Filter Topology TopologicalSpace
open scoped CStarAlgebra ComplexOrder
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
def sequence (φ : ℕ → Channel D A) : Channel D (NormUltrapower.BoundedSeq A) where
  linear := {
    toFun d := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun n => φ n d) ‖d‖ (fun n => (φ n).norm_le d)
    map_add' d e := by ext n; exact (φ n).linear.map_add d e
    map_smul' z d := by ext n; exact (φ n).linear.map_smul z d }
  norm_le d := (BoundedContinuousFunction.norm_le (norm_nonneg d)).mpr (fun n => (φ n).norm_le d)
  mul_eq d e := by ext n; exact (φ n).mul_eq d e
lemma sequence_apply (φ : ℕ → Channel D A) (d : D) (n : ℕ) : sequence φ d n=φ n d := rfl

def centralize (ω : Ultrafilter ℕ) (φ : Channel D (NormUltrapower.Algebra A ω))
    (hφ : ∀ d, φ d∈NormUltrapower.centralSubalgebra ω) :
    Channel D (NormUltrapower.CentralAlgebra A ω) where
  linear := {
    toFun d := ⟨φ d,hφ d⟩
    map_add' d e := Subtype.ext (φ.linear.map_add d e)
    map_smul' z d := Subtype.ext (φ.linear.map_smul z d) }
  norm_le d := φ.norm_le d
  mul_eq d e := Subtype.ext (φ.mul_eq d e)

lemma sequence_central [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) (φ : ℕ → Channel D A)
    (hφ : ∀ i d, Tendsto (fun n => ‖φ n d*denseSeq A i-denseSeq A i*φ n d‖) atTop (𝓝 0)) :
    ∀ d, postcompose (sequence φ) (NormUltrapower.quotientMap ω) d∈NormUltrapower.centralSubalgebra ω := by
  intro d
  rw [NormUltrapower.mem_central_iff]
  intro a
  let z := NormUltrapower.quotientMap ω (sequence φ d)
  change NormUltrapower.diagonal ω a*z=z*NormUltrapower.diagonal ω a
  refine (denseRange_denseSeq A).induction_on a
    (p := fun a => NormUltrapower.diagonal ω a*z=z*NormUltrapower.diagonal ω a)
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro i
  have hz := (hφ i d).mono_left (by simpa only [Nat.cofinite_eq_atTop] using hω)
  have he : sequence φ d*NormUltrapower.constantSeq (denseSeq A i)-
      NormUltrapower.constantSeq (denseSeq A i)*sequence φ d∈NormUltrapower.nullIdeal ω :=
    (NormUltrapower.mem_nullIdeal ω _).mpr hz
  have heq := Ideal.Quotient.eq.mpr he
  exact heq.symm


theorem no_central_character_of_finite_channels [TopologicalSpace.SeparableSpace A]
    (H : ∀ (F : Finset A) (ε : ℝ), 0<ε →
      ∃ φ ψ : Channel DimensionDrop23 A, φ 1+ψ 1=1 ∧
        ∀ a∈F, ∀ d : DimensionDrop23,
          ‖φ d*a-a*φ d‖≤ε*‖d‖ ∧ ‖ψ d*a-a*ψ d‖≤ε*‖d‖)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ) := by
  classical
  choose φ ψ hu hc using fun n : ℕ =>
    H ((Finset.range n).image (denseSeq A)) (1/((n:ℝ)+1)) (by positivity)
  have hz (r : ℕ → Channel DimensionDrop23 A)
      (hr : ∀ n i, i<n → ∀ d, ‖r n d*denseSeq A i-denseSeq A i*r n d‖≤(1/((n:ℝ)+1))*‖d‖) :
      ∀ i d, Tendsto (fun n => ‖r n d*denseSeq A i-denseSeq A i*r n d‖) atTop (𝓝 0) := by
    intro i d
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
      (g := fun n : ℕ => (1/((n:ℝ)+1))*‖d‖)
    · filter_upwards [eventually_gt_atTop i] with n hn
      exact hr n i hn d
    · simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖d‖
  have hl := sequence_central ω hω φ (hz φ (fun n i hi d =>
    (hc n (denseSeq A i) (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)) d).1))
  have hr := sequence_central ω hω ψ (hz ψ (fun n i hi d =>
    (hc n (denseSeq A i) (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)) d).2))
  let l := centralize ω (postcompose (sequence φ) (NormUltrapower.quotientMap ω)) hl
  let r := centralize ω (postcompose (sequence ψ) (NormUltrapower.quotientMap ω)) hr
  apply no_character_of_pair l r
  apply Subtype.ext
  change NormUltrapower.quotientMap ω (sequence φ 1)+NormUltrapower.quotientMap ω (sequence ψ 1)=1
  rw [←_root_.map_add,←_root_.map_one (NormUltrapower.quotientMap ω)]
  congr 1
  ext n
  exact hu n
end KirchbergRordam.MultiplicativeChannel
namespace KirchbergRordam.TensorHalfFlip
open Filter Topology
open scoped CStarAlgebra
universe u
variable {D C : Type u} [CStarAlgebra D] [CStarAlgebra C]
  [Nontrivial D] [Nontrivial C]


theorem injective_of_halfFlip (h : HalfFlip D) (φ : D →⋆ₐ[ℂ] C) :
    Function.Injective φ := by
  apply (injective_iff_map_eq_zero φ).mpr
  intro d hd
  let f : MaxTensor.Algebra D D →⋆ₐ[ℂ] MinTensor.Algebra C D :=
    MaxTensor.lift (MinTensor.includeLeft.comp φ) MinTensor.includeRight
      (fun a b => MinTensor.legs_commute (φ a) b)
  have hL (a : D) : f (MaxTensor.includeLeft a)=MinTensor.includeLeft (φ a) :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft _ _ _) a
  have hR (a : D) : f (MaxTensor.includeRight a)=MinTensor.includeRight a :=
    DFunLike.congr_fun (MaxTensor.lift_includeRight _ _ _) a
  obtain ⟨u,hu⟩ := h
  have ht := ((map_continuous f).tendsto _).comp (hu d)
  have hz (n : ℕ) : f (conj (u n) (MaxTensor.includeLeft d))=0 := by
    simp only [conj,Unitary.conjStarAlgAut_apply,map_mul,map_star,hL,hd,map_zero,mul_zero,zero_mul]
  change Tendsto (fun n => f (conj (u n) (MaxTensor.includeLeft d))) atTop
    (𝓝 (f (MaxTensor.includeRight d))) at ht
  simp only [hz,hR] at ht
  have he : MinTensor.includeRight (A:=C) d=0 :=
    (tendsto_nhds_unique tendsto_const_nhds ht).symm
  exact (MinTensor.includeRight_isometry (A:=C) (B:=D)).injective
    (he.trans (map_zero _).symm)
end KirchbergRordam.TensorHalfFlip
namespace KirchbergRordam.BalancedDropLimit
open Filter


theorem central_no_character (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (NormUltrapower.CentralAlgebra Algebra ω →⋆ₐ[ℂ] ℂ) :=
  MultiplicativeChannel.no_central_character_of_finite_channels
    BalancedDropChannels.finite_control ω hω
end KirchbergRordam.BalancedDropLimit
namespace KirchbergRordam
open Filter Topology NormUltrapower


theorem balanced_drop_character_criterion
    (A : Type) [CStarAlgebra A] [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (CentralAlgebra A ω →⋆ₐ[ℂ] ℂ) ↔
      Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A BalancedDropLimit.Algebra) := by
  constructor
  · intro hF
    obtain ⟨ι⟩ := BalancedDropLimit.to_central A ω hω hF
    obtain ⟨u,hu⟩ := BalancedDropHalfFlip.exists_half_flip
    exact spatial_absorption_of_central_maximal_half_flip A BalancedDropLimit.Algebra ω ι u hu
  · rintro ⟨θ⟩
    obtain ⟨e⟩ := central_isomorphism θ ω
    obtain ⟨r⟩ := minimal_tensor_central_right A BalancedDropLimit.Algebra ω
    have hF := BalancedDropLimit.central_no_character ω hω
    exact ⟨fun χ => hF.false ((χ.comp e.symm.toStarAlgHom).comp r)⟩
theorem balanced_drop_hom_injective {C : Type} [CStarAlgebra C] [Nontrivial C]
    (φ : BalancedDropLimit.Algebra →⋆ₐ[ℂ] C) : Function.Injective φ :=
  TensorHalfFlip.injective_of_halfFlip BalancedDropHalfFlip.exists_half_flip φ
end KirchbergRordam
end

end OAI
