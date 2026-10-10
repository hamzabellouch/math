import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveSupport

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma liveNormCap_power_bound (b Lcap Z r ell F eta tau : ℝ)
    (_hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hZ : 2 ≤ Z)
    (hr : r ≤ Lcap) (hell : ell ≤ Lcap) (hF : 0 ≤ F) (hFcap : F ≤ Lcap)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (htau : 0 ≤ tau) (htau1 : tau ≤ 1) :
    1 ≤ liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)) ∧
    liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)) ≤
      max 1 b * Z^(3*Lcap+16) := by
  have hz : 0<Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  have hb1 : 1 ≤ max 1 b := le_max_left _ _
  have hbmax : b ≤ max 1 b := le_max_right _ _
  have hpow (a : ℝ) (ha : a ≤ 3*Lcap+16) : Z^a ≤ max 1 b*Z^(3*Lcap+16) :=
    (Real.rpow_le_rpow_of_exponent_le hz1 ha).trans (le_mul_of_one_le_left (Real.rpow_nonneg hz.le _) hb1)
  have hsq : (Z^(ell+eta))^2=Z^(2*(ell+eta)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    ring
  refine ⟨(Real.one_le_rpow hz1 (by linarith : 0 ≤ 2*F+15*eta+tau)).trans (le_max_left _ _),?_⟩
  unfold liveNormCap
  apply max_le (hpow _ (by linarith))
  apply max_le
  · exact mul_le_mul hbmax (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
      (Real.rpow_nonneg hz.le _) (by linarith)
  apply max_le
  · rw [hsq,mul_assoc,←Real.rpow_add hz]
    exact mul_le_mul hbmax (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
      (Real.rpow_nonneg hz.le _) (by linarith)
  · rw [hsq]
    exact hpow _ (by linarith)

lemma dyadIndex_power_log_bound (b A : ℝ) (hb : 1 ≤ b) (hA : 0 ≤ A) :
    ∃ C : ℝ,0<C ∧ ∀ Z R : ℝ,2 ≤ Z → 1 ≤ R → R ≤ b*Z^A →
      ((dyadIndex R+1:ℕ):ℝ)^8 ≤ C*(1+Real.log Z)^8 := by
  let c := 1+Real.log b/Real.log 2+A/Real.log 2
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcb : 0 ≤ Real.log b/Real.log 2 := div_nonneg (Real.log_nonneg hb) hl2.le
  have hcA : 0 ≤ A/Real.log 2 := div_nonneg hA hl2.le
  have hc : 0<c := by dsimp [c];linarith
  refine ⟨c^8,pow_pos hc _,?_⟩
  intro Z R hZ hR hbound
  have hz : 0<Z := by linarith
  have hr : 0<R := by linarith
  have hb0 : 0<b := by linarith
  have hlz : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hf := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hR)
  have hl := Real.log_le_log hr hbound
  rw [Real.log_mul (ne_of_gt hb0) (ne_of_gt (Real.rpow_pos_of_pos hz _)),Real.log_rpow hz] at hl
  have hstep : ((dyadIndex R+1:ℕ):ℝ) ≤ c*(1+Real.log Z) := by
    simp only [Nat.cast_add,Nat.cast_one,dyadIndex,Real.logb] at *
    have hd := div_le_div_of_nonneg_right hl hl2.le
    have hmul : 0 ≤ (Real.log b/Real.log 2)*Real.log Z := mul_nonneg hcb hlz
    dsimp [c]
    have he : (Real.log b+A*Real.log Z)/Real.log 2=Real.log b/Real.log 2+(A/Real.log 2)*Real.log Z := by ring
    rw [he] at hd
    nlinarith
  calc
    _ ≤ (c*(1+Real.log Z))^8 := pow_le_pow_left₀ (by positivity) hstep 8
    _= _ := by rw [mul_pow]

theorem live_joint_scalar_log_budget (b Lcap : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) :
    ∃ C : ℝ,0<C ∧ ∀ Z r ell F eta tau : ℝ,2 ≤ Z → r ≤ Lcap → ell ≤ Lcap →
      0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      ((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)))+1:ℕ):ℝ)^8 ≤
        C*(1+Real.log Z)^8 := by
  obtain ⟨C,hC,hcount⟩ := dyadIndex_power_log_bound (max 1 b) (3*Lcap+16) (le_max_left _ _) (by linarith)
  refine ⟨C,hC,?_⟩
  intro Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1
  have hc := liveNormCap_power_bound b Lcap Z r ell F eta tau hb hcap hZ hr hell hF hFcap heta heta1 htau htau1
  exact hcount Z _ hZ hc.1 hc.2

lemma log_eighth_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z : ℝ,1 ≤ Z → (1+Real.log Z)^8 ≤ C*Z^ε := by
  let δ := ε/8
  have hd : 0<δ := by dsimp [δ];positivity
  refine ⟨(1+1/δ)^8,by positivity,?_⟩
  intro Z hZ
  have hz : 0<Z := by linarith
  have h1 := Real.one_le_rpow hZ hd.le
  have hl := Real.log_le_rpow_div hz.le hd
  have hb : 1+Real.log Z ≤ (1+1/δ)*Z^δ := by
    calc
      _ ≤ Z^δ+Z^δ/δ := add_le_add h1 hl
      _=_ := by ring
  calc
    _ ≤ ((1+1/δ)*Z^δ)^8 := pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hb 8
    _=(1+1/δ)^8*Z^ε := by
      have he : (Z^δ)^8=Z^ε := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
        congr 1
        dsimp [δ]
        ring
      rw [mul_pow,he]

theorem live_joint_scalar_small_power (b Lcap ε : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z r ell F eta tau : ℝ,2 ≤ Z → r ≤ Lcap → ell ≤ Lcap →
      0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      ((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)))+1:ℕ):ℝ)^8 ≤ C*Z^ε := by
  obtain ⟨C₁,hC₁,h₁⟩ := live_joint_scalar_log_budget b Lcap hb hcap
  obtain ⟨C₂,hC₂,h₂⟩ := log_eighth_small_power ε hε
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1
  exact (h₁ Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1).trans
    ((mul_le_mul_of_nonneg_left (h₂ Z (by linarith)) hC₁.le).trans_eq (mul_assoc _ _ _).symm)

theorem original_live_joint_small_power (b Lcap ε : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι → O)(hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (pool : Finset ι)(Q : Finset (ι→₀ℕ))(labels : Finset (Ideal O))
      (β : Ideal O → (ι→₀ℕ) → ℂ)(cutoff : CubeCoordinates ι → Finset ι → Ideal O → Finset ι → ℝ)
      (Ψ : O→*ℂ)(m : O)(mark : (ι→₀ℕ) → Finset ι → ℂ)(W : ℝ → ℂ)(Φ : 𝓢(ℝ,ℂ))
      (K Z r ell F eta tau theta : ℝ),
      2 ≤ Z → r ≤ Lcap → ell ≤ Lcap → 0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀y,W y≠0 → y ≤ b) →
      ((liveJointKeys p
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1)
          (Z^(2*F+15*eta+tau))) pool
        (sourceSummand p hp hcop hg β cutoff Ψ m mark
          (fun y=>CompletedHeight.normTwistedSource W theta (y/Z^r)) Φ K)).card:ℝ) ≤ C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := live_joint_scalar_small_power b Lcap ε hb hcap hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg pool Q labels β cutoff Ψ m mark W Φ K Z r ell F eta tau theta
    hZ hr hell hF hFcap heta heta1 htau htau1 hQ hlabels hW
  have hz : 0<Z := by linarith
  have he := original_twisted_live_joint_card p hp hcop hg pool Q labels (Z^(2*F+15*eta+tau))
    β cutoff Ψ m mark W Φ K b (Z^(ell+eta)) (Z^r) theta
    (Real.rpow_pos_of_pos hz _) (Real.rpow_nonneg hz.le _) hQ hlabels hW
  have he' : ((liveJointKeys p
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1)
          (Z^(2*F+15*eta+tau))) pool
        (sourceSummand p hp hcop hg β cutoff Ψ m mark
          (fun y=>CompletedHeight.normTwistedSource W theta (y/Z^r)) Φ K)).card:ℝ) ≤
      (((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau))))+1:ℕ):ℝ)^8 := by exact_mod_cast he
  exact he'.trans (hcount Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1)

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
