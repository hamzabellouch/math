import OAI.NumberTheory.DirichletL.Moments.SourceSupportedTailUniform
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import OAI.NumberTheory.DirichletL.Moments.NaturalRadialCutoff
import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def plainControl (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)):ℝ:=
  (∏i,s.M i)*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂

omit [DecidableEq ι] in
lemma plainControl_nonneg (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)):0≤plainControl s W₁ W₂:=by
  unfold plainControl
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _=>(s.M_ge_one i).trans' zero_le_one))
    (apply_nonneg _ _)) (apply_nonneg _ _)

omit [DecidableEq ι] in
lemma volume_pos (s:Input ι):0<volume s.toData:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

omit [DecidableEq ι] in
theorem input_mass (hi:ι→ℝ)(whi:ℝ)(hhi:∀i,0≤hi i)(hwhi:0≤whi)
    (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0<wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤hi i)(R seed:Ideal O):
    (∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      (2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2)*plainControl s W₁ W₂*volume s.toData:=by
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hm:=profile_mass_explicit s.W W₁ W₂ hi s.M whi whi
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    hhi hwhi hwhi (fun i=>zero_le_one.trans (s.M_ge_one i))
    (apply_nonneg _ _) (apply_nonneg _ _) hz (hzW W₁ hs₁) (hzW W₂ hs₂)
    (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) s.W_bound
    (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    R s.ν s.ν_bound s.P s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero
    rfl s.same_product (Fintype.piFinset s.pools)
  have hc:=finiteColumnCoefficient_mass (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  unfold coefficient
  rw [he₁,he₂]
  change (∑I∈_,‖finiteColumnCoefficient _ _ I‖)≤_
  apply (hc.trans hm).trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,plainControl,volume]
  ring

omit [DecidableEq ι] in
lemma input_column_bound (hi:ι→ℝ)(whi:ℝ)
    (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0<wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤hi i)(R seed I:Ideal O)(hn:coefficient s R seed I≠0):
    (Ideal.absNorm I:ℝ)≤((∏i,hi i)*whi^2)*volume s.toData:=by
  obtain ⟨v,hv,hv0,hvI⟩:=finiteColumnCoefficient_witness _ _ I hn
  have hz (i:ι):s.W i 0=0:=by
    by_contra h
    exact (not_le_of_gt (s.lo_pos i)) (s.support i h).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra h
    exact (not_le_of_gt hwlo) (hs h).1
  unfold coefficient at hn
  rw [he₁,he₂] at hv0
  have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
    hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv0
  rw [hvI] at hp
  apply hp.2.trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,volume]
  ring

lemma kernel_inverse_cap (HN Z B Tsec:ℝ)(hZ:1≤Z)(hB:0≤B)(hT:0<Tsec)(hcap:Tsec≤Z^B):
    ((min 1 (kernelReference Tsec HN))^2)⁻¹≤
      (1+Real.exp (2*HN))^2*(Z^B)^2:=by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hpow:1≤Z^B:=Real.one_le_rpow hZ hB
  have he:0<Real.exp (2*HN):=Real.exp_pos _
  have hb:(min 1 (kernelReference Tsec HN))⁻¹≤(1+Real.exp (2*HN))*Z^B:=by
    rw [min_def]
    split_ifs with h
    · simp only [inv_one]
      nlinarith
    · have hi:(kernelReference Tsec HN)⁻¹=Tsec*Real.exp (2*HN):=by
        unfold kernelReference
        rw [show -2*HN= -(2*HN) by ring,Real.exp_neg]
        field_simp
      rw [hi]
      calc
        _≤Z^B*Real.exp (2*HN):=mul_le_mul_of_nonneg_right hcap he.le
        _≤_:=by nlinarith [Real.rpow_pos_of_pos hz B]
  rw [←inv_pow]
  exact (pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt (lt_min zero_lt_one (kernelReference_pos Tsec HN hT)))) hb 2).trans_eq (mul_pow _ _ _)

lemma eventually_tail_threshold (HN ξ:ℝ)(hξ:0<ξ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ 2*HN/Real.log Z+Real.log (4:ℝ)/Real.log Z<ξ/4:=by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop ((2*HN+Real.log (4:ℝ))/(ξ/4)))] with Z hZ hlog
  refine ⟨hZ,?_⟩
  rw [←add_div]
  apply (div_lt_iff₀ (Real.log_pos hZ)).mpr
  have ht:0<ξ/4:=by linarith
  have hh:2*HN+Real.log (4:ℝ)<Real.log Z*(ξ/4):=(div_lt_iff₀ ht).mp hlog
  nlinarith

lemma choose_tail_order (B ξ saving:ℝ)(hB:0≤B)(hξ:0<ξ):
    ∃Adec:ℕ,∀(HN Z V Tsec:ℝ),1≤Z→0<V→V≤Z^B→0<Tsec→Tsec≤Z^B→
      V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹≤
        (1+Real.exp (2*HN))^2*Z^(-saving):=by
  obtain ⟨Adec,hAdec⟩:=exists_nat_ge ((5*B+saving)/(ξ/4))
  have horder:5*B-(ξ/4)*(Adec:ℝ)≤-saving:=by
    have hh:5*B+saving≤(Adec:ℝ)*(ξ/4):=(div_le_iff₀ (by linarith:0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro HN Z V Tsec hZ hV hVcap hT hTcap
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hk:=kernel_inverse_cap HN Z B Tsec hZ hB hT hTcap
  have hd:=reciprocal_cutoff_bound Z (ξ/4) Adec hz
  calc
    _≤(Z^B)^3*((1+Real.exp (2*HN))^2*(Z^B)^2)*Z^(-(ξ/4)*(Adec:ℝ)):=by
      apply mul_le_mul _ hd (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hV.le hVcap 3) hk
        (inv_nonneg.mpr (sq_nonneg _)) (by positivity)
    _=(1+Real.exp (2*HN))^2*Z^(5*B-(ξ/4)*(Adec:ℝ)):=by
      rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le]
      norm_num only [Nat.cast_ofNat]
      rw [show Z^(B*(3:ℝ))*((1+Real.exp (2*HN))^2*Z^(B*(2:ℝ)))*Z^(-(ξ/4)*(Adec:ℝ))=
        (1+Real.exp (2*HN))^2*(Z^(B*3)*Z^(B*2)*Z^(-(ξ/4)*(Adec:ℝ))) by ring]
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)

omit [DecidableEq ι] in
theorem second_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=second_discarded_energy_bound Adec
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)^2*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      Cmass*plainControl s W₁ W₂*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (input_column_bound hi whi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn hnom (by simpa using hZ.2)
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0<min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)^2*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hsquare hK.le
    _=(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end SevenEighths.CenteredMomentSourceInputTailUniform

end

end OAI
