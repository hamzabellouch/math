import OAI.Analysis.Littlewood.AlmostSign

namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators
lemma unitCircle_parameter {z : ℂ} (hz : ‖z‖=1) :
    ∃ t∈Set.Icc (0:ℝ) 1, z=realPhase (2*Real.pi*t) := by
  let Z : Circle := ⟨z,by change dist z 0=1; simpa using hz⟩
  let u := (AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero).symm Z
  let t := AddCircle.equivIco (1:ℝ) 0 u
  refine ⟨t.val,⟨t.property.1,by simpa using t.property.2.le⟩,?_⟩
  have hu : (t.val : UnitAddCircle)=u := AddCircle.coe_equivIco
  have hs : Circle.exp (2*Real.pi*t.val)=Z := by
    rw [show 2*Real.pi*t.val=2*Real.pi/(1:ℝ)*t.val by ring]
    rw [← AddCircle.toCircle_apply_mk,hu,← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply Z
  have hcoe := congrArg (fun w : Circle ↦ (w : ℂ)) hs
  simpa only [Circle.coe_exp,realPhase,mul_comm] using hcoe.symm

lemma littlewood_phase {N : ℕ} (X : Fin N → ℝ) (t : ℝ) :
    littlewoodValue X (realPhase (2*Real.pi*t))=
      ∑ k : Fin N, (X k : ℂ)*realPhase (2*Real.pi*t*k) := by
  unfold littlewoodValue
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [realPhase,← Complex.exp_nat_mul,realPhase]
  congr 1
  push_cast
  ring

end
end AsymptoticallyMinimalLittlewood
namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped Topology
open Filter

lemma entropy_small_defect {δ N u : ℝ} (hδ : 0<δ) (hδ20 : δ<1/20)
    (hN : 0<N) (hu : 0≤u) (hub : u≤4*δ*N) :
    u*Real.log (80*N/u)≤4*δ*N*Real.log (20/δ) := by
  have hlog2 : (1/2:ℝ)≤Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this ⊢
    exact this
  have hL : 1≤Real.log (20/δ) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4)
      (show 4≤20/δ by apply (le_div_iff₀ hδ).mpr; linarith)
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    norm_num at hh
    linarith
  by_cases hz : u=0
  · rw [hz]
    simp only [zero_mul]
    positivity
  have hup : 0<u := lt_of_le_of_ne hu (Ne.symm hz)
  have hb : 0<4*δ*N := by positivity
  have hsplit : Real.log (80*N/u)=Real.log (20/δ)+Real.log ((4*δ*N)/u) := by
    rw [← Real.log_mul (by positivity : 20/δ≠0) (by positivity : (4*δ*N)/u≠0)]
    congr 1
    field_simp
    ring
  have hs : u*Real.log ((4*δ*N)/u)≤4*δ*N-u := by
    calc
      _ ≤ u*((4*δ*N)/u-1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (by positivity)) hu
      _ = _ := by field_simp
  have hm := mul_le_mul_of_nonneg_right hub (sub_nonneg.mpr hL)
  rw [hsplit,mul_add]
  nlinarith

lemma small_delta_budget {η : ℝ} (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ<1/20 ∧
      Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ))<1+η/2 := by
  let f (x : ℝ) := Real.sqrt ((1+x)^3/(1-x))+
    393216*Real.sqrt (x*Real.log 20-x*Real.log x)
  have hf : ContinuousAt f 0 := by
    apply ContinuousAt.add
    · exact Real.continuous_sqrt.continuousAt.comp
        (((continuousAt_const.add continuousAt_id).pow 3).div
          (continuousAt_const.sub continuousAt_id) (by norm_num))
    · exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
        ((continuousAt_id.mul continuousAt_const).sub Real.continuous_mul_log.continuousAt))
  have hf0 : f 0=1 := by norm_num [f]
  obtain ⟨r,hr,hh⟩ := Metric.continuousAt_iff.mp hf (η/2) (by positivity)
  let δ := min (r/2) (1/40)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδ20 : δ<1/20 := (min_le_right _ _).trans_lt (by norm_num)
  have hδr : δ<r := (min_le_left _ _).trans_lt (by linarith)
  have hd : dist δ (0:ℝ)<r := by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using hδr
  have hval := hh hd
  rw [hf0,Real.dist_eq] at hval
  have he : f δ=Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ)) := by
    dsimp [f]
    rw [Real.log_div (by norm_num : (20:ℝ)≠0) hδ.ne',mul_sub]
  refine ⟨δ,hδ,hδ20,?_⟩
  rw [he] at hval
  have := (abs_lt.mp hval).2
  linarith

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

lemma defect_from_energy {N : ℕ} (_hN : 1≤N) {δ : ℝ} (X : Fin N → ℝ)
    (hX : ∀ k, |X k|≤1)
    (hE : (1-8*δ)*(N : ℝ)≤∑ k, (X k)^2) :
    0≤defectMass X ∧ defectMass X≤4*δ*N := by
  have hμ : 0≤defectMass X := div_nonneg
    (Finset.sum_nonneg (fun k _ ↦ sub_nonneg.mpr (hX k))) (by norm_num)
  have hs : (∑ k, (1-|X k|))≤∑ k, (1-(X k)^2) := by
    apply Finset.sum_le_sum
    intro k _
    have hh := mul_nonneg (abs_nonneg (X k)) (sub_nonneg.mpr (hX k))
    nlinarith [sq_abs (X k)]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at hs
  refine ⟨hμ,?_⟩
  dsimp [defectMass]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one]
  nlinarith

/-- At a fixed positive length, energy and the full-circle relaxed bound imply
an actual real signing with the stated normalized error. -/
lemma round_sample_once {N : ℕ} (hN : 1≤N) {δ K C : ℝ}
    (hδ : 0<δ) (hδ20 : δ<1/20) (X : Fin N → ℝ)
    (hX : ∀ k, |X k|≤1)
    (hE : (1-8*δ)*(N : ℝ)≤∑ k, (X k)^2)
    (hmax : ∀ t∈Set.Icc (0:ℝ) 1,
      ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N, (X k : ℂ)*realPhase (2*Real.pi*t*k)‖≤K+C/N) :
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧ ∀ z : ℂ, ‖z‖=1 →
      ‖littlewoodValue ε z‖/Real.sqrt N≤
        K+C/N+196608*(1/Real.sqrt N+2*Real.sqrt (δ*Real.log (20/δ))) := by
  obtain ⟨ε,hε,hround⟩ := defect_rounding hN X hX
  refine ⟨ε,hε,?_⟩
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNs : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hDL : 0≤δ*Real.log (20/δ) := mul_nonneg hδ.le
    (Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith)))
  obtain ⟨hμ0,hμb⟩ := defect_from_energy hN X hX hE
  have hentr := entropy_small_defect hδ hδ20 hNr hμ0 hμb
  have hroot : Real.sqrt (defectMass X*Real.log (80*(N : ℝ)/defectMass X))≤
      2*Real.sqrt (δ*Real.log (20/δ))*Real.sqrt N := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow,mul_pow,Real.sq_sqrt hDL,Real.sq_sqrt hNr.le]
    nlinarith
  intro z hz
  obtain ⟨t,ht,rfl⟩ := unitCircle_parameter hz
  have hm := hmax t ht
  rw [← littlewood_phase] at hm
  have hn : ‖(1/(Real.sqrt N : ℂ))*littlewoodValue X (realPhase (2*Real.pi*t))‖=
      ‖littlewoodValue X (realPhase (2*Real.pi*t))‖/Real.sqrt N := by
    rw [norm_mul,norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hNs]
    ring
  rw [hn] at hm
  have hr := hround (realPhase (2*Real.pi*t)) (by simp)
  have hr' : ‖littlewoodValue ε (realPhase (2*Real.pi*t))-
      littlewoodValue X (realPhase (2*Real.pi*t))‖≤
        196608*(1+2*Real.sqrt (δ*Real.log (20/δ))*Real.sqrt N) := by
    exact hr.trans (by nlinarith)
  have hd := div_le_div_of_nonneg_right hr' hNs.le
  have he : (196608*(1+2*Real.sqrt (δ*Real.log (20/δ))*Real.sqrt N))/Real.sqrt N=
      196608*(1/Real.sqrt N+2*Real.sqrt (δ*Real.log (20/δ))) := by
    field_simp
  rw [he] at hd
  have ht := div_le_div_of_nonneg_right
    (norm_le_norm_sub_add (littlewoodValue ε (realPhase (2*Real.pi*t)))
      (littlewoodValue X (realPhase (2*Real.pi*t)))) hNs.le
  rw [add_div] at ht
  linarith

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

theorem main : MainStatement := by
  intro η hη
  obtain ⟨δ,hδ,hδ20,hbudget⟩ := small_delta_budget hη
  obtain ⟨X,L,C,hC,hL,hX,hE,hmax⟩ := almost_sign_sampler hδ hδ20
  let B := Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ))
  have hB : B<1+η := by dsimp [B]; linarith
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hinv : Tendsto (fun N : ℕ ↦ 1/Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp hsqrt) using 1
    funext N
    simp only [Function.comp_apply,one_div]
  have hrem : Tendsto (fun N : ℕ ↦ C/(N : ℝ)+196608*(1/Real.sqrt (N : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat C).add (hinv.const_mul 196608)
  have her : ∀ᶠ N : ℕ in atTop,
      C/(N : ℝ)+196608*(1/Real.sqrt (N : ℝ))<1+η-B :=
    hrem.eventually (gt_mem_nhds (sub_pos.mpr hB))
  have hen : ∀ᶠ N : ℕ in atTop, 1-8*δ<(∑ k, (X N k)^2)/(N : ℝ) :=
    hE.eventually (lt_mem_nhds (show 1-8*δ<L by linarith))
  have hall : ∀ᶠ N : ℕ in atTop,
      1≤N ∧ 1-8*δ<(∑ k, (X N k)^2)/(N : ℝ) ∧
        C/(N : ℝ)+196608*(1/Real.sqrt (N : ℝ))<1+η-B := by
    filter_upwards [eventually_ge_atTop (1:ℕ),hen,her] with N hN hn hr
    exact ⟨hN,hn,hr⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hall
  refine ⟨N₀,(hN₀ N₀ le_rfl).1,?_⟩
  intro N hN
  obtain ⟨hN1,hen,her⟩ := hN₀ N hN
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hener : (1-8*δ)*(N : ℝ)≤∑ k, (X N k)^2 :=
    ((lt_div_iff₀ hNr).mp hen).le
  obtain ⟨ε,hε,hεb⟩ := round_sample_once hN1 hδ hδ20 (X N) (hX N hN1)
    hener (hmax N hN1)
  refine ⟨ε,hε,?_⟩
  intro z hz
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hNr)).mp
  have hb := hεb z hz
  dsimp [B] at her
  linarith

end
end AsymptoticallyMinimalLittlewood

end OAI
