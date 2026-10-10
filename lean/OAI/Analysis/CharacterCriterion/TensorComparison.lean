import OAI.Analysis.CharacterCriterion.MinTensor

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

namespace KirchbergRordam.Representations
open scoped InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
lemma gnsVector_norm_sq (φ : A →ₚ[ℂ] ℂ) (a : A) :
    ‖gnsVector φ a‖ ^ 2 = ‖φ (star a*a)‖ := by
  rw [← gnsVector_inner]
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_sq]
lemma gnsVector_unit_norm (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1) :
    ‖gnsVector φ 1‖ = 1 := by
  have h := gnsVector_norm_sq φ 1
  simp only [star_one,one_mul,hφ,norm_one] at h
  nlinarith [norm_nonneg (gnsVector φ 1)]
lemma gnsVector_norming_norm (φ : A →ₚ[ℂ] ℂ) (a : A)
    (ha : ‖φ (star a*a)‖=‖a‖^2) : ‖gnsVector φ a‖ = ‖a‖ := by
  have h := (gnsVector_norm_sq φ a).trans ha
  nlinarith [norm_nonneg (gnsVector φ a),norm_nonneg a]
end KirchbergRordam.Representations
namespace KirchbergRordam.MinTensor
open scoped TensorProduct InnerProductSpace
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
lemma RepresentationPair.tmul_norm (ρ : RepresentationPair A B) (a : A) (b : B) :
    ρ.crossSeminorm.toSeminorm (a ⊗ₜ[ℂ] b) =
      ‖Spatial.map (ρ.leftRep a) (ρ.rightRep b)‖ := by
  change ‖ρ.left a * ρ.right b‖ = _
  change ‖Spatial.map (ρ.leftRep a) 1 * Spatial.map 1 (ρ.rightRep b)‖ = _
  rw [← Spatial.map_mul, mul_one,one_mul]


theorem norm_tmul [Nontrivial A] [Nontrivial B] (a : A) (b : B) :
    ‖of (rawEquiv (a ⊗ₜ[ℂ] b))‖ = ‖a‖ * ‖b‖ := by
  rw [norm_of]
  apply le_antisymm (seminorm_tmul_le a b)
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  obtain ⟨φ,hφ,hφa⟩ := States.exists_norming_state A a
  obtain ⟨ψ,hψ,hψb⟩ := States.exists_norming_state B b
  let ρ : RepresentationPair A B := {
    H := φ.GNS
    K := ψ.GNS
    normH := inferInstance
    innerH := inferInstance
    completeH := inferInstance
    normK := inferInstance
    innerK := inferInstance
    completeK := inferInstance
    leftRep := φ.gnsStarAlgHom
    rightRep := ψ.gnsStarAlgHom }
  let ξ : Spatial.Hilbert φ.GNS ψ.GNS :=
    ((Representations.gnsVector φ 1) ⊗ₜ[ℂ] (Representations.gnsVector ψ 1) : φ.GNS ⊗[ℂ] ψ.GNS)
  have hnξ : ‖ξ‖=1 := by
    simp only [ξ,UniformSpace.Completion.norm_coe,TensorProduct.norm_tmul,
      Representations.gnsVector_unit_norm φ hφ,Representations.gnsVector_unit_norm ψ hψ,
      one_mul]
  have heval : Spatial.map (φ.gnsStarAlgHom a) (ψ.gnsStarAlgHom b) ξ =
      ((Representations.gnsVector φ a) ⊗ₜ[ℂ] (Representations.gnsVector ψ b) : φ.GNS ⊗[ℂ] ψ.GNS) := by
    simp only [ξ, Spatial.map_coe,TensorProduct.mapL_tmul,
      Representations.gnsVector_apply,mul_one]
  have hbound : ‖a‖*‖b‖ ≤ ‖Spatial.map (φ.gnsStarAlgHom a) (ψ.gnsStarAlgHom b)‖ := by
    calc
      ‖a‖*‖b‖ = ‖Spatial.map (φ.gnsStarAlgHom a) (ψ.gnsStarAlgHom b) ξ‖ := by
        rw [heval,UniformSpace.Completion.norm_coe,TensorProduct.norm_tmul,
          Representations.gnsVector_norming_norm φ a hφa,
          Representations.gnsVector_norming_norm ψ b hψb]
      _ ≤ ‖Spatial.map (φ.gnsStarAlgHom a) (ψ.gnsStarAlgHom b)‖*‖ξ‖ :=
        ContinuousLinearMap.le_opNorm _ ξ
      _ = _ := by rw [hnξ,mul_one]
  apply hbound.trans
  calc
    _ = ρ.crossSeminorm.toSeminorm (a ⊗ₜ[ℂ] b) := (ρ.tmul_norm a b).symm
    _ ≤ seminorm (a ⊗ₜ[ℂ] b) := le_seminorm (some ρ) _
lemma includeLeft_isometry [Nontrivial A] [Nontrivial B] :
    Isometry (includeLeft (A := A) (B := B)) := by
  apply AddMonoidHomClass.isometry_of_norm includeLeft
  intro a
  change ‖of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))‖ = ‖a‖
  rw [norm_tmul,norm_one,mul_one]
lemma includeRight_isometry [Nontrivial A] [Nontrivial B] :
    Isometry (includeRight (A := A) (B := B)) := by
  apply AddMonoidHomClass.isometry_of_norm includeRight
  intro b
  change ‖of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b))‖ = ‖b‖
  rw [norm_tmul,norm_one,one_mul]
end KirchbergRordam.MinTensor
namespace KirchbergRordam
section
universe u
open Filter Topology NormUltrapower


theorem spatial_absorption_of_central_maximal_half_flip
    (A D : Type u) [CStarAlgebra A] [CStarAlgebra D]
    [Nontrivial A] [Nontrivial D]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace D]
    (ω : Ultrafilter ℕ) (ι : D →⋆ₐ[ℂ] CentralAlgebra A ω)
    (u : ℕ → unitary (MaxTensor.Algebra D D))
    (hu : ∀ d, Tendsto (fun n => Unitary.conjStarAlgAut ℂ _ (u n)
      (MaxTensor.includeLeft d)) atTop (𝓝 (MaxTensor.includeRight d))) :
    Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A D) := by
  classical
  let B := MaxTensor.Algebra A D
  let : TopologicalSpace.SeparableSpace B := MaxTensor.separable_maxTensor
  let φ : A →⋆ₐ[ℂ] B := MaxTensor.includeLeft
  let r : D →⋆ₐ[ℂ] B := MaxTensor.includeRight
  let ι₀ : D →⋆ₐ[ℂ] NormUltrapower.Algebra A ω := (centralSubalgebra ω).subtype.comp ι
  have hc (a : A) (d : D) : Commute (NormUltrapower.diagonal ω a) (ι₀ d) :=
    (mem_central_iff ω (ι d : NormUltrapower.Algebra A ω)).mp (ι d).property a
  let ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω := MaxTensor.lift (NormUltrapower.diagonal ω) ι₀ hc
  have hs (a : A) : ψ (φ a)=NormUltrapower.diagonal ω a :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft (NormUltrapower.diagonal ω) ι₀ hc) a
  have hsR (d : D) : ψ (r d)=ι₀ d :=
    DFunLike.congr_fun (MaxTensor.lift_includeRight (NormUltrapower.diagonal ω) ι₀ hc) d
  have hφ : Function.Injective φ := by
    intro a b hab
    apply (diagonal_isometry ω).injective
    rw [← hs a,← hs b,hab]
  let L : D →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := (NormUltrapower.map φ ω).comp ι₀
  let R : D →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := (NormUltrapower.diagonal ω).comp r
  have hLR (d e : D) : Commute (L d) (R e) := ultrapower_left_commutes_right ω (ι₀ d) e
  let U : MaxTensor.Algebra D D →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := MaxTensor.lift L R hLR
  have hUL (d : D) : U (MaxTensor.includeLeft d)=L d :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft L R hLR) d
  have hUR (d : D) : U (MaxTensor.includeRight d)=R d :=
    DFunLike.congr_fun (MaxTensor.lift_includeRight L R hLR) d
  let v : ℕ → unitary (NormUltrapower.Algebra B ω) := fun n => ⟨U (u n),Unitary.map_mem U (u n).property⟩
  have hUa (a : A) (x : MaxTensor.Algebra D D) : Commute (NormUltrapower.diagonal ω (φ a)) (U x) := by
    apply maximal_lift_image_commutes L R hLR
    · intro d
      have he := congrArg (NormUltrapower.map φ ω) (hc a d).eq
      change NormUltrapower.diagonal ω (φ a)*NormUltrapower.map φ ω (ι₀ d) =
        NormUltrapower.map φ ω (ι₀ d)*NormUltrapower.diagonal ω (φ a)
      simpa only [map_mul,map_diagonal] using he
    · intro d
      exact (MaxTensor.legs_commute a d).map (NormUltrapower.diagonal ω)
  let F : ℕ → B →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := fun n =>
    (Unitary.conjStarAlgAut ℂ _ (v n)).toStarAlgHom.comp ((NormUltrapower.map φ ω).comp ψ)
  have hFL (a : A) : Tendsto (fun n => F n (φ a)) atTop (𝓝 (NormUltrapower.diagonal ω (φ a))) := by
    have he (n : ℕ) : F n (φ a)=NormUltrapower.diagonal ω (φ a) := by
      change Unitary.conjStarAlgAut ℂ _ (v n) (NormUltrapower.map φ ω (ψ (φ a)))=_
      rw [hs,map_diagonal,Unitary.conjStarAlgAut_apply]
      change U (u n)*NormUltrapower.diagonal ω (φ a)*star (U (u n))=NormUltrapower.diagonal ω (φ a)
      rw [← (hUa a (u n)).eq,mul_assoc]
      have hv : U (u n)*star (U (u n))=1 := (v n).property.2
      rw [hv,mul_one]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => NormUltrapower.diagonal ω (φ a)) atTop (𝓝 (NormUltrapower.diagonal ω (φ a))))
  have hFR (d : D) : Tendsto (fun n => F n (r d)) atTop (𝓝 (NormUltrapower.diagonal ω (r d))) := by
    have he (n : ℕ) : F n (r d)=U (Unitary.conjStarAlgAut ℂ _ (u n) (MaxTensor.includeLeft d)) := by
      change Unitary.conjStarAlgAut ℂ _ (v n) (NormUltrapower.map φ ω (ψ (r d)))=_
      rw [hsR]
      simp only [Unitary.conjStarAlgAut_apply,map_mul,map_star,hUL]
      rfl
    have hU : LipschitzWith 1 U := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one,one_mul]
      rw [dist_eq_norm,← map_sub,dist_eq_norm]
      exact NonUnitalStarAlgHom.norm_apply_le U (x-y)
    have ht := (hU.continuous.tendsto (MaxTensor.includeRight d)).comp (hu d)
    rw [hUR] at ht
    change Tendsto (fun n => U (Unitary.conjStarAlgAut ℂ _ (u n) (MaxTensor.includeLeft d)))
      atTop (𝓝 (NormUltrapower.diagonal ω (r d))) at ht
    exact ht.congr (fun n => (he n).symm)
  have hF := MaxTensor.pointwise_limit_of_tensor_legs F (NormUltrapower.diagonal ω) hFL hFR
  let q : B →⋆ₐ[ℂ] MinTensor.Algebra A D := MinTensor.fromMaximal
  have hqd : DenseRange q := MinTensor.fromMaximal_denseRange
  have hqL : LipschitzWith 1 q := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul]
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact NonUnitalStarAlgHom.norm_apply_le q (x-y)
  let : TopologicalSpace.SeparableSpace (MinTensor.Algebra A D) :=
    hqd.separableSpace hqL.continuous
  have hleg : q.comp φ = MinTensor.includeLeft :=
    MaxTensor.lift_includeLeft MinTensor.includeLeft MinTensor.includeRight MinTensor.legs_commute
  have hqi : Function.Injective (q.comp φ) := by
    rw [hleg]
    exact MinTensor.includeLeft_isometry.injective
  apply quotient_isomorphism_of_ultrapower_split_and_conjugacy ω φ q hqd hqi ψ hs
  intro T ε hε
  have htest (b : B) (_ : b ∈ T) : ∀ᶠ n in atTop, dist (F n b) (NormUltrapower.diagonal ω b)<ε :=
    (hF b).eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨n,hn⟩ := (T.eventually_all.mpr htest).exists
  exact ⟨v n,hn⟩
end
universe u
open Filter Topology NormUltrapower


theorem balanced_drop_absorption
    (A : Type) [CStarAlgebra A] [Nontrivial A]
    [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.cofinite)
    (hF : IsEmpty (CentralAlgebra A ω →⋆ₐ[ℂ] ℂ)) :
    Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A BalancedDropLimit.Algebra) := by
  obtain ⟨ι⟩ := BalancedDropLimit.to_central A ω hω hF
  obtain ⟨u,hu⟩ := BalancedDropHalfFlip.exists_half_flip
  exact spatial_absorption_of_central_maximal_half_flip A BalancedDropLimit.Algebra ω ι u hu
end KirchbergRordam
namespace KirchbergRordam.MaxTensor
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]
instance nontrivial_of_spatial : Nontrivial (Algebra A B) :=
  (MinTensor.fromMaximal (A:=A) (B:=B)).toRingHom.domain_nontrivial
lemma includeLeft_isometry : Isometry (includeLeft (A:=A) (B:=B)) := by
  apply NonUnitalStarAlgHom.isometry
  intro a b h
  apply (MinTensor.includeLeft_isometry (A:=A) (B:=B)).injective
  have he := congrArg (MinTensor.fromMaximal (A:=A) (B:=B)) h
  have hl (x : A) : MinTensor.fromMaximal (MaxTensor.includeLeft x)=MinTensor.includeLeft (B:=B) x :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft MinTensor.includeLeft MinTensor.includeRight MinTensor.legs_commute) x
  simpa only [hl] using he
end KirchbergRordam.MaxTensor

end

end OAI
