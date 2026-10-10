import OAI.NumberTheory.DirichletL.Moments.RadialSourceDictionary
import OAI.NumberTheory.DirichletL.Moments.ActiveCanonicalSource

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Input (ι:Type*) [Fintype ι] extends Data ι where
  plain₁ : Finset (Ideal O)
  plain₂ : Finset (Ideal O)
  plain₁_ne : ∀I∈plain₁,I≠0
  plain₂_ne : ∀I∈plain₂,I≠0
  coverage₁ : PlainCoverage plain₁ W₁ 1 X₁ Y₁
  coverage₂ : PlainCoverage plain₂ W₂ 1 X₂ Y₂
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  lower : ℝ
  upper : ℝ
  lower_pos : 0<lower
  lower_le : ∀i,lower≤lo i
  upper_ge : ∀i,hi i≤upper

 def Input.pools (s:Input ι) : (ι⊕Fin 2)→Finset (Ideal O) :=
  Sum.elim s.slots (fun j=>if j=0 then s.plain₁ else s.plain₂)

omit [DecidableEq ι] in
lemma Input.pools_ne (s:Input ι) (j:ι⊕Fin 2) : ∀I∈s.pools j,I≠0 := by
  cases j with
  | inl i => exact fun I hI=>(s.prime i I hI).ne_zero
  | inr j =>
    fin_cases j
    · simpa [Input.pools] using s.plain₁_ne
    · simpa [Input.pools] using s.plain₂_ne

omit [DecidableEq ι] in
lemma Input.slot_support (s:Input ι) (i:ι) : Function.support (s.W i)⊆Set.Icc s.lower s.upper :=
  fun _x hx=>⟨(s.lower_le i).trans (s.support i hx).1,((s.support i hx).2).trans (s.upper_ge i)⟩

omit [DecidableEq ι] in
lemma alloc_ne (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : B.val j≠0 :=
  (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 j

omit [DecidableEq ι] in
lemma alloc_norm_pos (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : (0:ℝ)<Ideal.absNorm (B.val j) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))

 def commonData (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) : Data (liveIndices B.val) where
  η:=s.η
  m:=fixedBadMask*idealGenerator (R*C)
  A:=1
  t:=s.t
  slots:=fun i=>s.slots i.val
  prime:=fun i I hI=>s.prime i.val I hI
  ν:=fun i=>s.ν i.val
  W:=fun i=>s.W i.val
  lo:=fun i=>s.lo i.val
  hi:=fun i=>s.hi i.val
  P:=fun i=>s.P i.val
  lo_pos:=fun i=>s.lo_pos i.val
  P_pos:=fun i=>s.P_pos i.val
  support:=fun i=>s.support i.val
  W₁:=s.W₁
  W₂:=s.W₂
  X₁:=s.X₁/Ideal.absNorm (B.val (Sum.inr 0))
  X₂:=s.X₂/Ideal.absNorm (B.val (Sum.inr 1))
  Y₁:=s.Y₁/Ideal.absNorm (B.val (Sum.inr 0))
  Y₂:=s.Y₂/Ideal.absNorm (B.val (Sum.inr 1))
  M:=fun i=>s.M i.val
  M_ge_one:=fun i=>s.M_ge_one i.val
  coefficient_bound:=fun i I hI=>s.coefficient_bound i.val I hI
  b₁:=s.b₁
  b₂:=s.b₂
  support₁:=s.support₁
  support₂:=s.support₂
  X₁_pos:=div_pos s.X₁_pos (alloc_norm_pos s C B _)
  X₂_pos:=div_pos s.X₂_pos (alloc_norm_pos s C B _)
  Y₁_pos:=div_pos s.Y₁_pos (alloc_norm_pos s C B _)
  Y₂_pos:=div_pos s.Y₂_pos (alloc_norm_pos s C B _)
  same_product:=by rw [div_mul_div_comm,div_mul_div_comm,s.same_product]
  rows:=∅
  weight:=fun _=>0
  weight_nonneg:=by simp

omit [DecidableEq ι] in
lemma common_profile_le (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) :
    (commonData s C R B).profileFactor≤s.toData.profileFactor := by
  unfold Data.profileFactor
  change (2*(max 1 s.b₁*max 1 s.b₂))*(∏i:liveIndices B.val,s.M i.val)^2≤_
  rw [Finset.prod_coe_sort]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

end SevenEighths.CenteredMomentCommonRadialData

end

end OAI
