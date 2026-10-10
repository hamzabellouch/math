import OAI.Analysis.CharacterCriterion.PrimePresentation

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

namespace KirchbergRordam.PrimeDropPresentation.Channels
open MatrixDiagonalPath DiagonalIteration PrimeDropPresentation.Iteration
open GeneralDropSystem DropChannels
open BalancedDropSystem (half)
variable (S : PrimeDropPresentation)
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology

def finalPath (n k : ℕ) := normalizedPath S n (k+1)
def endPath (n k : ℕ) (t : unitInterval) := finalPath S n k t*star (finalPath S n k 1)
lemma endPath_continuous (n k : ℕ) : Continuous (endPath S n k) :=
  (normalizedPath_continuous S n (k+1)).mul continuous_const
@[simp] lemma endPath_one (n k : ℕ) : endPath S n k 1=1 := mul_inv_cancel _
def stageLeft (n k : ℕ) : Channel DimensionDrop23 (S.Stage (n+k+1)) :=
  DropChannels.left (S.size (n+k+1)) (S.size (n+k+1)+1)
    (finalPath S n k) (normalizedPath_continuous S n (k+1)) (normalizedPath_zero S n (k+1))
    (zeroRep S (n+k) (normalizedPath S n k half))
def stageRight (n k : ℕ) : Channel DimensionDrop23 (S.Stage (n+k+1)) :=
  DropChannels.right (S.size (n+k+1)) (S.size (n+k+1)+1)
    (endPath S n k) (endPath_continuous S n k) (endPath_one S n k)
    (oneRep S (n+k)
      (normalizedPath S n k half*star (normalizedPath S n k 1)))
lemma stage_unit_sum (n k : ℕ) : stageLeft S n k 1+stageRight S n k 1=1 :=
  DropChannels.unit_sum _ _ _ _ _ _ _ _ _ _
lemma map_next (n k : ℕ) (x : S.Stage n) :
    S.chain.map n (n+k+1) (by omega) x =
      step (S.stepData (n+k))
        (S.chain.map n (n+k) (Nat.le_add_right n k) x) := by
  rw [S.chain.map_succ n (n+k) (Nat.le_add_right n k)]
  rfl
lemma stageLeft_bound (n k : ℕ) (x : S.Stage n) {ε : ℝ} (hε : 0≤ε)
    (hp : ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε)
    (hf : ∀ t : unitInterval,
      ‖conj (star (finalPath S n k t))
        ((S.chain.map n (n+k+1) (by omega) x).val t)-
        (S.chain.map n (n+k+1) (by omega) x).val 0‖≤ε)
    (d : DimensionDrop23) :
    ‖stageLeft S n k d * (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x)-
      (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x) * stageLeft S n k d‖≤4*ε*‖d‖ := by
  let g : S.Stage (n+k+1) := S.chain.map n (n+k+1) (by omega) x
  change ‖((stageLeft S n k d*g-g*stageLeft S n k d).val)‖≤_
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖(leftScalar t • conj (finalPath S n k t)
      (MatrixTensor.leftMatrix (zeroRep S (n+k) (normalizedPath S n k half) d))) * g.val t-
    g.val t*(leftScalar t • conj (finalPath S n k t)
      (MatrixTensor.leftMatrix (zeroRep S (n+k) (normalizedPath S n k half) d)))‖≤_
  apply (smul_commutator _ _ _ (leftScalar_norm t)).trans
  let ρ : DimensionDrop23 →⋆ₐ[ℂ] MatrixTensor.Mat (Fin (S.size (n+k+1)) × Fin (S.size (n+k+1)+1)) := MatrixTensor.leftMatrix.comp
    (zeroRep S (n+k) (normalizedPath S n k half))
  have he := zeroRep_bound S (n+k) (normalizedPath S n k half)
    (S.chain.map n (n+k) (Nat.le_add_right n k) x) d (hp half)
  rw [←map_next S n k x] at he
  have ht := transport_bound ρ d (finalPath S n k t) (g.val t) (g.val 0) hε (hf t) he
  convert ht using 1 <;> first | rfl | ring
lemma stageRight_bound (n k : ℕ) (x : S.Stage n) {ε : ℝ} (hε : 0≤ε)
    (hp : ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε)
    (hf : ∀ t : unitInterval,
      ‖conj (star (finalPath S n k t))
        ((S.chain.map n (n+k+1) (by omega) x).val t)-
        (S.chain.map n (n+k+1) (by omega) x).val 0‖≤ε)
    (d : DimensionDrop23) :
    ‖stageRight S n k d * (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x)-
      (show S.Stage (n+k+1) from S.chain.map n (n+k+1) (by omega) x) * stageRight S n k d‖≤8*ε*‖d‖ := by
  let f : S.Stage (n+k) := S.chain.map n (n+k) (Nat.le_add_right n k) x
  let g : S.Stage (n+k+1) := S.chain.map n (n+k+1) (by omega) x
  have hm : ‖conj (star (normalizedPath S n k half*star (normalizedPath S n k 1)))
      (f.val half)-f.val 1‖≤2*ε := by
    rw [norm_twisted_difference]
    exact BalancedDropChannels.norm_sub_two _ _ _ (hp half) (hp 1)
  have he := oneRep_bound S (n+k)
    (normalizedPath S n k half*star (normalizedPath S n k 1)) f d hm
  change _ ≤ 2*(2*ε)*‖d‖ at he
  rw [show 2*(2*ε)*‖d‖=(4*ε)*‖d‖ by ring] at he
  dsimp only [f] at he
  rw [←map_next S n k x] at he
  change ‖((stageRight S n k d*g-g*stageRight S n k d).val)‖≤_
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖(rightScalar t • conj (endPath S n k t)
      (MatrixTensor.rightMatrix (oneRep S (n+k)
        (normalizedPath S n k half*star (normalizedPath S n k 1)) d))) * g.val t-
    g.val t*(rightScalar t • conj (endPath S n k t)
      (MatrixTensor.rightMatrix (oneRep S (n+k)
        (normalizedPath S n k half*star (normalizedPath S n k 1)) d)))‖≤_
  apply (smul_commutator _ _ _ (rightScalar_norm t)).trans
  let ρ : DimensionDrop23 →⋆ₐ[ℂ] MatrixTensor.Mat (Fin (S.size (n+k+1)) × Fin (S.size (n+k+1)+1)) := MatrixTensor.rightMatrix.comp (oneRep S (n+k)
    (normalizedPath S n k half*star (normalizedPath S n k 1)))
  have ht : ‖conj (star (endPath S n k t)) (g.val t)-g.val 1‖≤2*ε := by
    rw [endPath,norm_twisted_difference]
    exact BalancedDropChannels.norm_sub_two _ _ _ (hf t) (hf 1)
  have hc := transport_bound ρ d (endPath S n k t) (g.val t) (g.val 1) (by positivity : 0≤2*ε) ht he
  convert hc using 1 <;> first | rfl | ring
end KirchbergRordam.PrimeDropPresentation.Channels
namespace KirchbergRordam.PrimeDropPresentation.Channels
open PrimeDropPresentation.Iteration
variable (S : PrimeDropPresentation)
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology
lemma finite_stage (n : ℕ) (F : Finset (S.Stage n)) (ε : ℝ) (hε : 0<ε) :
    ∃ φ ψ : Channel DimensionDrop23 S.Algebra, φ 1+ψ 1=1 ∧
      ∀ x∈F, ∀ d : DimensionDrop23,
        ‖φ d*S.inclusion n x-S.inclusion n x*φ d‖≤ε*‖d‖ ∧
        ‖ψ d*S.inclusion n x-S.inclusion n x*ψ d‖≤ε*‖d‖ := by
  have he : ∀ᶠ k in atTop, ∀ x∈F, ∀ t : unitInterval,
      ‖DiagonalIteration.conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) x).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) x).val 0‖≤ε/8 := by
    apply (Filter.eventually_all_finset F).mpr
    intro x hx
    exact eventually_untwist_small S n x (ε/8) (by positivity)
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp he
  let φ := MultiplicativeChannel.postcompose (stageLeft S n K) (S.inclusion (n+K+1))
  let ψ := MultiplicativeChannel.postcompose (stageRight S n K) (S.inclusion (n+K+1))
  refine ⟨φ,ψ,?_,fun x hx d => ?_⟩
  · change S.inclusion _ (stageLeft S n K 1)+S.inclusion _ (stageRight S n K 1)=1
    rw [←map_add,stage_unit_sum S,map_one]
  · have hl := stageLeft_bound S n K x (by positivity : 0≤ε/8) (hK K le_rfl x hx)
      (hK (K+1) (Nat.le_succ K) x hx) d
    have hr := stageRight_bound S n K x (by positivity : 0≤ε/8) (hK K le_rfl x hx)
      (hK (K+1) (Nat.le_succ K) x hx) d
    have hm : S.inclusion (n+K+1) (S.chain.map n (n+K+1) (by omega) x)=S.inclusion n x :=
      S.inclusion_map n (n+K+1) (by omega) x
    have hc (r : S.Stage (n+K+1)) := DropChannels.commutator_map_bound
      (S.inclusion (n+K+1)) r (S.chain.map n (n+K+1) (by omega) x)
    have hcl := (hc (stageLeft S n K d)).trans hl
    have hcr := (hc (stageRight S n K d)).trans hr
    rw [hm] at hcl hcr
    change _≤_ at hcl
    refine ⟨hcl.trans ?_,hcr.trans ?_⟩ <;> nlinarith [norm_nonneg d]

lemma channel_perturbation (φ : Channel DimensionDrop23 S.Algebra) (d : DimensionDrop23)
    (x y : S.Algebra) :
    ‖φ d*x-x*φ d‖≤‖φ d*y-y*φ d‖+2*‖x-y‖*‖d‖ := by
  calc
    _ ≤ ‖φ d*y-y*φ d‖+2*‖x-y‖*‖φ d‖ := DropChannels.norm_commutator_change (φ d) x y
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (φ.norm_le d)
      (by positivity : 0≤2*‖x-y‖))

lemma finite_control (F : Finset S.Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ φ ψ : Channel DimensionDrop23 S.Algebra, φ 1+ψ 1=1 ∧
      ∀ x∈F, ∀ d : DimensionDrop23,
        ‖φ d*x-x*φ d‖≤ε*‖d‖ ∧ ‖ψ d*x-x*ψ d‖≤ε*‖d‖ := by
  classical
  obtain ⟨n,a,ha⟩ := PrimeDropPresentation.HalfFlip.common_stage S F (ε/4) (by positivity)
  obtain ⟨φ,ψ,hu,h⟩ := finite_stage S n (F.image a) (ε/2) (by positivity)
  refine ⟨φ,ψ,hu,fun x hx d => ?_⟩
  have hb := h (a x) (Finset.mem_image_of_mem a hx) d
  have hd := (ha x hx).le
  rw [norm_sub_rev] at hd
  constructor
  · have hc := channel_perturbation S φ d x (S.inclusion n (a x))
    nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg d),hb.1]
  · have hc := channel_perturbation S ψ d x (S.inclusion n (a x))
    nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg d),hb.2]
end KirchbergRordam.PrimeDropPresentation.Channels
namespace KirchbergRordam.PrimeDropPresentation
open Filter
variable (S : PrimeDropPresentation)


theorem central_no_character (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (NormUltrapower.CentralAlgebra S.Algebra ω →⋆ₐ[ℂ] ℂ) :=
  MultiplicativeChannel.no_central_character_of_finite_channels
    (Channels.finite_control S) ω hω


theorem character_criterion
    (A : Type) [CStarAlgebra A] [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ) ↔
      Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A S.Algebra) := by
  constructor
  · intro hF
    obtain ⟨ι⟩ := S.to_central A ω hω hF
    obtain ⟨u,hu⟩ := HalfFlip.exists_half_flip S
    exact spatial_absorption_of_central_maximal_half_flip A S.Algebra ω ι u hu
  · rintro ⟨θ⟩
    obtain ⟨e⟩ := central_isomorphism θ ω
    obtain ⟨r⟩ := minimal_tensor_central_right A S.Algebra ω
    have hF := S.central_no_character ω hω
    exact ⟨fun χ => hF.false ((χ.comp e.symm.toStarAlgHom).comp r)⟩


theorem equiv (T : PrimeDropPresentation) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ)≤cofinite) : Nonempty (S.Algebra ≃⋆ₐ[ℂ] T.Algebra) := by
  obtain ⟨e⟩ := (T.character_criterion S.Algebra ω hω).mp (S.central_no_character ω hω)
  obtain ⟨f⟩ := (S.character_criterion T.Algebra ω hω).mp (T.central_no_character ω hω)
  exact ⟨e.trans (MinTensor.flip.trans f.symm)⟩

theorem equiv_balanced (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    Nonempty (S.Algebra ≃⋆ₐ[ℂ] BalancedDropLimit.Algebra) := by
  obtain ⟨e⟩ := (balanced_drop_character_criterion S.Algebra ω hω).mp
    (S.central_no_character ω hω)
  obtain ⟨f⟩ := (S.character_criterion BalancedDropLimit.Algebra ω hω).mp
    (BalancedDropLimit.central_no_character ω hω)
  exact ⟨e.trans (MinTensor.flip.trans f.symm)⟩
theorem hom_injective {C : Type} [CStarAlgebra C] [Nontrivial C]
    (φ : S.Algebra →⋆ₐ[ℂ] C) : Function.Injective φ :=
  TensorHalfFlip.injective_of_halfFlip (HalfFlip.exists_half_flip S) φ
end KirchbergRordam.PrimeDropPresentation
end

end OAI
