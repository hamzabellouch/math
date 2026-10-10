import OAI.Analysis.AllenCahn.Modica

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open scoped ENNReal

def interfaceNormal {n : ℕ} (v : Space n → ℝ) (z : Space n) : Space n :=
  ‖gradient (inverseProfile v) z‖⁻¹ • gradient (inverseProfile v) z

def regularZeroSet {n : ℕ} (v : Space n → ℝ) : Set (Space n) :=
  {z | v z=0 ∧ gradient (inverseProfile v) z≠0}

def chordDirection {n : ℕ} (z y : Space n) : Space n := ‖y-z‖⁻¹ • (y-z)

def chordAngle {n : ℕ} (v : Space n → ℝ) (z y : Space n) : ℝ :=
  |inner ℝ (interfaceNormal v z) (chordDirection z y)|

def reachChordValue {n : ℕ} (Γ : ℝ → ℝ) (v : Space n → ℝ) (z y : Space n) : ℝ≥0∞ :=
  if y=z ∨ chordAngle v z y=0 then ⊤
  else ENNReal.ofReal (‖y-z‖*Γ (chordAngle v z y))

def penalizedReach {n : ℕ} (Γ : ℝ → ℝ) (v : Space n → ℝ) (z : Space n) : ℝ≥0∞ :=
  ⨅ y : {y : Space n // v y=0}, reachChordValue Γ v z y

def OffDiagonalActive {n : ℕ} (Γ : ℝ → ℝ) (v : Space n → ℝ) (z y : Space n) : Prop :=
  z∈regularZeroSet v ∧ v y=0 ∧ y≠z ∧ 0<chordAngle v z y ∧
    reachChordValue Γ v z y=penalizedReach Γ v z

lemma interfaceNormal_norm {n : ℕ} {v : Space n → ℝ} {z : Space n}
    (hz : z∈regularZeroSet v) : ‖interfaceNormal v z‖=1 := by
  rw [interfaceNormal,norm_smul,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz.2)]

lemma chordDirection_norm {n : ℕ} {z y : Space n} (h : y≠z) :
    ‖chordDirection z y‖=1 := by
  rw [chordDirection,norm_smul,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))]

lemma chordAngle_le_one {n : ℕ} {v : Space n → ℝ} {z y : Space n}
    (hz : z∈regularZeroSet v) (hy : y≠z) : chordAngle v z y≤1 := by
  have H := abs_real_inner_le_norm (interfaceNormal v z) (chordDirection z y)
  simpa only [interfaceNormal_norm hz,chordDirection_norm hy,mul_one,chordAngle] using H

lemma chord_backwards {n : ℕ} (y N : Space n) (hN : ‖N‖=1) {s t : ℝ} (hst : s<t) :
    ‖(y+s•N)-(y+t•N)‖=t-s ∧
      chordDirection (y+t•N) (y+s•N)= -N := by
  have he : (y+s•N)-(y+t•N)=(s-t)•N := by module
  have hnorm : ‖(y+s•N)-(y+t•N)‖=t-s := by
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_neg (sub_neg.mpr hst),hN,mul_one]
    ring
  refine ⟨hnorm,?_⟩
  rw [chordDirection,hnorm,he,smul_smul]
  have hc : (t-s)⁻¹*(s-t)= -1 := by
    field_simp [ne_of_gt (sub_pos.mpr hst)]
    ring
  rw [hc,neg_one_smul]

lemma active_contact_no_nearer_zero_on_ray {n : ℕ} {v : Space n → ℝ} {Γ : ℝ → ℝ}
    (hΓ : ∀ s, 0<s → s≤1 → s⁻¹≤Γ s)
    {y N : Space n} (hN : ‖N‖=1) {s t : ℝ} (hs : 0<s) (hst : s<t)
    (hactive : OffDiagonalActive Γ v (y+t•N) y) : v (y+s•N)≠0 := by
  intro hzero
  have ht : 0<t := hs.trans hst
  obtain ⟨hr,hy,hyne,ha,hact⟩ := hactive
  have hany := iInf_le (fun z : {z : Space n // v z=0} =>
    reachChordValue Γ v (y+t•N) z) ⟨y+s•N,hzero⟩
  change penalizedReach Γ v (y+t•N) ≤ reachChordValue Γ v (y+t•N) (y+s•N) at hany
  rw [← hact] at hany
  obtain ⟨hnorm1,hdir1⟩ := chord_backwards y N hN hst
  obtain ⟨hnorm0,hdir0⟩ := chord_backwards y N hN (s:=0) ht
  simp only [zero_smul,add_zero,sub_zero] at hnorm0 hdir0
  have hangle : chordAngle v (y+t•N) (y+s•N)=chordAngle v (y+t•N) y := by
    simp only [chordAngle,hdir1,hdir0]
  have hne : y+s•N≠y+t•N := by
    intro he
    have hh : ‖(y+s•N)-(y+t•N)‖=0 := by rw [he,sub_self,norm_zero]
    linarith
  have hg : 0<Γ (chordAngle v (y+t•N) y) :=
    lt_of_lt_of_le (inv_pos.mpr ha) (hΓ _ ha (chordAngle_le_one hr hyne))
  simp only [reachChordValue,hyne,ha.ne',or_self,ite_false,hne,hangle,hnorm0,hnorm1] at hany
  have hstrict : ENNReal.ofReal ((t-s)*Γ (chordAngle v (y+t•N) y)) <
      ENNReal.ofReal (t*Γ (chordAngle v (y+t•N) y)) := by
    apply ENNReal.ofReal_lt_ofReal_iff'.mpr
    constructor <;> nlinarith
  exact not_lt_of_ge hany hstrict

lemma active_bases_on_ray_unique {n : ℕ} {v : Space n → ℝ} {Γ : ℝ → ℝ}
    (hΓ : ∀ a, 0<a → a≤1 → a⁻¹≤Γ a)
    {y N : Space n} (hN : ‖N‖=1) {s t : ℝ} (hs : 0<s) (ht : 0<t)
    (hsact : OffDiagonalActive Γ v (y+s•N) y)
    (htact : OffDiagonalActive Γ v (y+t•N) y) : s=t := by
  rcases lt_trichotomy s t with h|h|h
  · exact False.elim ((active_contact_no_nearer_zero_on_ray hΓ hN hs h htact) hsact.1.1)
  · exact h
  · exact False.elim ((active_contact_no_nearer_zero_on_ray hΓ hN ht h hsact) htact.1.1)

lemma active_ray_subsingleton {n : ℕ} {v : Space n → ℝ} {Γ : ℝ → ℝ}
    (hΓ : ∀ a, 0<a → a≤1 → a⁻¹≤Γ a) {y N : Space n} (hN : ‖N‖=1) :
    Set.Subsingleton {z | ∃ t : ℝ, 0<t ∧ z=y+t•N ∧ OffDiagonalActive Γ v z y} := by
  rintro z ⟨s,hs,rfl,has⟩ w ⟨t,ht,rfl,hat⟩
  rw [active_bases_on_ray_unique hΓ hN hs ht has hat]

lemma chordAngle_mul_length {n : ℕ} (v : Space n → ℝ) {z y : Space n} (hy : y≠z) :
    chordAngle v z y*‖y-z‖=|inner ℝ (interfaceNormal v z) (y-z)| := by
  have hl : ‖y-z‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
  simp only [chordAngle,chordDirection,inner_smul_right,abs_mul,abs_inv,
    abs_of_nonneg (norm_nonneg _)]
  field_simp

lemma reach_chord_inequality {n : ℕ} {v : Space n → ℝ} {Γ : ℝ → ℝ} {C : ℝ}
    (hC : 0<C) (hΓ0 : ∀ s, 0<s → s≤1 → 0≤Γ s)
    (hΓ : ∀ s, 0<s → s≤1 → Γ s≤C/s)
    {z : Space n} (hz : z∈regularZeroSet v) {y : Space n} (hy : v y=0) :
    (penalizedReach Γ v z).toReal*|inner ℝ (interfaceNormal v z) (y-z)|≤C*‖y-z‖^2 := by
  by_cases hyz : y=z
  · subst y
    simp
  have hl : 0<‖y-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
  have ha0 : 0≤chordAngle v z y := abs_nonneg _
  have ha1 := chordAngle_le_one hz hyz
  have halink := chordAngle_mul_length v hyz
  by_cases ha : chordAngle v z y=0
  · rw [ha,zero_mul] at halink
    rw [←halink,mul_zero]
    positivity
  have hap : 0<chordAngle v z y := lt_of_le_of_ne ha0 (Ne.symm ha)
  have hg0 := hΓ0 _ hap ha1
  have hi := iInf_le (fun w : {w : Space n // v w=0}=>reachChordValue Γ v z w) ⟨y,hy⟩
  change penalizedReach Γ v z≤reachChordValue Γ v z y at hi
  simp only [reachChordValue,hyz,ha,or_self,ite_false] at hi
  have hir := ENNReal.toReal_mono (by exact ENNReal.ofReal_ne_top) hi
  rw [ENNReal.toReal_ofReal (mul_nonneg hl.le hg0)] at hir
  have hg := (le_div_iff₀ hap).mp (hΓ _ hap ha1)
  have hh : (penalizedReach Γ v z).toReal*chordAngle v z y≤C*‖y-z‖ := by
    calc
      _ ≤ (‖y-z‖*Γ (chordAngle v z y))*chordAngle v z y :=
        mul_le_mul_of_nonneg_right hir hap.le
      _ = ‖y-z‖*(Γ (chordAngle v z y)*chordAngle v z y) := by ring
      _ ≤ ‖y-z‖*C := mul_le_mul_of_nonneg_left hg hl.le
      _ = _ := by ring
  have hh' := mul_le_mul_of_nonneg_right hh hl.le
  rw [mul_assoc,halink] at hh'
  nlinarith [hh']

lemma reach_tangent_ball_zero_free {n : ℕ} {v : Space n → ℝ} {Γ : ℝ → ℝ} {C : ℝ}
    (hC : 0<C) (hΓ0 : ∀ s, 0<s → s≤1 → 0≤Γ s)
    (hΓ : ∀ s, 0<s → s≤1 → Γ s≤C/s)
    {z : Space n} (hz : z∈regularZeroSet v) {r : ℝ} (hr : 0<r)
    (hd : 2*C*r≤(penalizedReach Γ v z).toReal) {σ : ℝ} (hσ : |σ|=1) :
    ∀ x∈Metric.ball (z+(σ*r)•interfaceNormal v z) r, v x≠0 := by
  intro x hx hvx
  have hn := interfaceNormal_norm hz
  have hs : σ^2=1 := by nlinarith [sq_abs σ]
  have hball := Metric.mem_ball.mp hx
  rw [dist_eq_norm] at hball
  have hsq : ‖x-(z+(σ*r)•interfaceNormal v z)‖^2<r^2 :=
    sq_lt_sq₀ (norm_nonneg _) hr.le |>.mpr hball
  have he : x-(z+(σ*r)•interfaceNormal v z)=(x-z)-(σ*r)•interfaceNormal v z := by module
  rw [he,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,abs_mul,hσ,one_mul,abs_of_pos hr,
    hn,mul_one,inner_smul_right] at hsq
  have hins : inner ℝ (x-z) (interfaceNormal v z)=inner ℝ (interfaceNormal v z) (x-z) :=
    real_inner_comm _ _
  rw [hins] at hsq
  have hinner : σ*inner ℝ (interfaceNormal v z) (x-z)≤
      |inner ℝ (interfaceNormal v z) (x-z)| := by
    calc
      _ ≤ |σ*inner ℝ (interfaceNormal v z) (x-z)| := le_abs_self _
      _ = _ := by rw [abs_mul,hσ,one_mul]
  have hc := reach_chord_inequality hC hΓ0 hΓ hz hvx
  have hmul := mul_le_mul_of_nonneg_right hd (abs_nonneg (inner ℝ (interfaceNormal v z) (x-z)))
  have hstrict : ‖x-z‖^2<2*r*|inner ℝ (interfaceNormal v z) (x-z)| := by
    nlinarith [mul_le_mul_of_nonneg_left hinner (by positivity : 0≤2*r)]
  have hstrictC := mul_lt_mul_of_pos_left hstrict hC
  nlinarith

lemma penalized_normal_map_injective {n : ℕ} {v : Space n → ℝ} {Γ : ℝ → ℝ} {C : ℝ}
    (hC : 0<C) (hΓ0 : ∀ a, 0<a → a≤1 → 0≤Γ a)
    (hΓ : ∀ a, 0<a → a≤1 → Γ a≤C/a)
    {z w : Space n} (hz : z∈regularZeroSet v) (hw : w∈regularZeroSet v)
    {t s : ℝ} (ht : 4*C*|t|≤(penalizedReach Γ v z).toReal)
    (hs : 4*C*|s|≤(penalizedReach Γ v w).toReal)
    (heq : z+t•interfaceNormal v z=w+s•interfaceNormal v w) : z=w ∧ t=s := by
  have hzch := reach_chord_inequality hC hΓ0 hΓ hz hw.1
  have hwch := reach_chord_inequality hC hΓ0 hΓ hw hz.1
  have hneg : z-w= -(w-z) := by module
  rw [hneg,norm_neg,inner_neg_right,abs_neg] at hwch
  have hzt := mul_le_mul_of_nonneg_right ht
    (abs_nonneg (inner ℝ (interfaceNormal v z) (w-z)))
  have hws := mul_le_mul_of_nonneg_right hs
    (abs_nonneg (inner ℝ (interfaceNormal v w) (w-z)))
  have hza : 4*|t| * |inner ℝ (interfaceNormal v z) (w-z)|≤‖w-z‖^2 := by
    have H := hzt.trans hzch
    nlinarith
  have hwa : 4*|s| * |inner ℝ (interfaceNormal v w) (w-z)|≤‖w-z‖^2 := by
    have H := hws.trans hwch
    nlinarith
  have hd : w-z=t•interfaceNormal v z-s•interfaceNormal v w := by
    calc
      _ = (w+s•interfaceNormal v w)-(z+s•interfaceNormal v w) := by module
      _ = _ := by rw [←heq]; module
  have hi : ‖w-z‖^2=t*inner ℝ (interfaceNormal v z) (w-z)-
      s*inner ℝ (interfaceNormal v w) (w-z) := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rw 1 [hd]
    simp only [inner_sub_left,real_inner_smul_left]
  have hti : t*inner ℝ (interfaceNormal v z) (w-z)≤
      |t| * |inner ℝ (interfaceNormal v z) (w-z)| := by
    simpa only [abs_mul] using (le_abs_self (t*inner ℝ (interfaceNormal v z) (w-z)))
  have hsi : -(s*inner ℝ (interfaceNormal v w) (w-z))≤
      |s| * |inner ℝ (interfaceNormal v w) (w-z)| := by
    simpa only [abs_mul] using (neg_le_abs (s*inner ℝ (interfaceNormal v w) (w-z)))
  have hn : ‖w-z‖=0 := by nlinarith [norm_nonneg (w-z)]
  have hzw : z=w := (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
  refine ⟨hzw,?_⟩
  subst w
  have he : (t-s)•interfaceNormal v z=0 := by
    have hh := add_left_cancel heq
    rw [sub_smul,hh,sub_self]
  have hh := congrArg norm he
  rw [norm_smul,Real.norm_eq_abs,interfaceNormal_norm hz,mul_one,norm_zero] at hh
  exact sub_eq_zero.mp (abs_eq_zero.mp hh)

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open scoped ENNReal

lemma quadratic_residual_of_lipschitz_fderiv {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) {K : NNReal} {z y : Space n} {r : ℝ} (hr : 0<r)
    (hL : LipschitzOnWith K (fderiv ℝ f) (Metric.ball z r))
    (hy : y∈Metric.ball z r) :
    |f y-f z-fderiv ℝ f z (y-z)|≤(K:ℝ)*‖y-z‖^2 := by
  let g : Space n → ℝ := fun x=>f x-fderiv ℝ f z (x-z)
  have hd (x : Space n) : HasFDerivAt g (fderiv ℝ f x-fderiv ℝ f z) x := by
    exact (hf x).hasFDerivAt.sub ((fderiv ℝ f z).hasFDerivAt.comp x (hasFDerivAt_id x |>.sub_const z))
  have hsub : Metric.closedBall z ‖y-z‖ ⊆ Metric.ball z r := by
    intro x hx
    apply Metric.mem_ball.mpr
    exact (Metric.mem_closedBall.mp hx).trans_lt (by simpa [dist_eq_norm] using hy)
  have hb (x : Space n) (hx : x∈Metric.closedBall z ‖y-z‖) :
      ‖fderiv ℝ f x-fderiv ℝ f z‖≤(K:ℝ)*‖y-z‖ := by
    calc
      _ ≤ (K:ℝ)*‖x-z‖ := hL.norm_sub_le (hsub hx) (Metric.mem_ball_self hr)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hx) K.coe_nonneg
  have H := (convex_closedBall z ‖y-z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _=>(hd x).hasFDerivWithinAt) hb (Metric.mem_closedBall_self (norm_nonneg _))
    (by simp [Metric.mem_closedBall,dist_eq_norm] : y∈Metric.closedBall z ‖y-z‖)
  have he : g y-g z=f y-f z-fderiv ℝ f z (y-z) := by
    dsimp [g]
    simp only [sub_self,map_zero,sub_zero]
    ring
  rw [he,Real.norm_eq_abs] at H
  convert H using 1
  ring

lemma regular_zero_local_chord_bound {n : ℕ} {v : Space n → ℝ}
    (hU : ContDiff ℝ 2 (inverseProfile v)) {z : Space n} (hz : z∈regularZeroSet v) :
    ∃ r B : ℝ, 0<r ∧ 0<B ∧ ∀ y∈Metric.ball z r, v y=0 →
      |inner ℝ (interfaceNormal v z) (y-z)|≤B*‖y-z‖^2 := by
  have hU1 : ContDiff ℝ 1 (fderiv ℝ (inverseProfile v)) := hU.fderiv_right (by norm_num)
  obtain ⟨K,t,ht,hK⟩ := hU1.contDiffAt (x:=z) |>.exists_lipschitzOnWith
  obtain ⟨r,hr,hrt⟩ := Metric.mem_nhds_iff.mp ht
  have hgrad : 0<‖gradient (inverseProfile v) z‖ := norm_pos_iff.mpr hz.2
  refine ⟨r,((K:ℝ)+1)/‖gradient (inverseProfile v) z‖,hr,by positivity,?_⟩
  intro y hy hvy
  have H := quadratic_residual_of_lipschitz_fderiv (hU.differentiable (by norm_num)) hr (hK.mono hrt) hy
  have hUz : inverseProfile v z=0 := by simp [inverseProfile,hz.1]
  have hUy : inverseProfile v y=0 := by simp [inverseProfile,hvy]
  rw [hUy,hUz,sub_self,zero_sub,abs_neg] at H
  have he : |inner ℝ (interfaceNormal v z) (y-z)|=
      |fderiv ℝ (inverseProfile v) z (y-z)|/‖gradient (inverseProfile v) z‖ := by
    simp [interfaceNormal,real_inner_smul_left,inner_gradient_left,abs_mul,abs_inv,
      abs_of_pos hgrad,div_eq_mul_inv,mul_comm]
  rw [he]
  apply (div_le_div_of_nonneg_right H hgrad.le).trans
  have hh : (K:ℝ)*‖y-z‖^2≤((K:ℝ)+1)*‖y-z‖^2 := by nlinarith [sq_nonneg ‖y-z‖]
  simpa [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hh hgrad.le

lemma penalizedReach_pos {n : ℕ} {v : Space n → ℝ} {Γ : ℝ → ℝ}
    (hU : ContDiff ℝ 2 (inverseProfile v))
    (hΓ : ∀ a, 0<a → a≤1 → a⁻¹≤Γ a)
    {z : Space n} (hz : z∈regularZeroSet v) : 0<penalizedReach Γ v z := by
  obtain ⟨r,B,hr,hB,hbound⟩ := regular_zero_local_chord_bound hU hz
  let c := min r B⁻¹
  have hc : 0<c := lt_min hr (inv_pos.mpr hB)
  have H : ENNReal.ofReal c ≤ penalizedReach Γ v z := by
    apply le_iInf
    rintro ⟨y,hy⟩
    change ENNReal.ofReal c≤reachChordValue Γ v z y
    by_cases hi : y=z ∨ chordAngle v z y=0
    · simp [reachChordValue,hi]
    simp only [reachChordValue,hi,ite_false]
    apply ENNReal.ofReal_le_ofReal
    have hyz : y≠z := fun hh=>hi (Or.inl hh)
    have ha : 0<chordAngle v z y :=
      lt_of_le_of_ne (abs_nonneg _) (Ne.symm (fun hh=>hi (Or.inr hh)))
    have ha1 := chordAngle_le_one hz hyz
    have hΓ1 : 1≤Γ (chordAngle v z y) :=
      (one_le_inv₀ ha |>.mpr ha1).trans (hΓ _ ha ha1)
    have hl : 0<‖y-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
    by_cases hyr : y∈Metric.ball z r
    · have hb := hbound y hyr hy
      rw [←chordAngle_mul_length v hyz] at hb
      have hab : chordAngle v z y≤B*‖y-z‖ := by nlinarith
      have hg := hΓ _ ha ha1
      have hg' : 1≤Γ (chordAngle v z y)*chordAngle v z y := by
        have := mul_le_mul_of_nonneg_right hg ha.le
        simpa [ne_of_gt ha] using this
      have hprod : 1≤B*(‖y-z‖*Γ (chordAngle v z y)) := by
        have hh := mul_le_mul_of_nonneg_left hab (zero_le_one.trans hΓ1)
        nlinarith
      have hcost : B⁻¹≤‖y-z‖*Γ (chordAngle v z y) := by
        rw [inv_eq_one_div]
        exact (div_le_iff₀ hB).mpr (by simpa [mul_comm] using hprod)
      exact (min_le_right _ _).trans hcost
    · have hr' : r≤‖y-z‖ := by simpa [Metric.mem_ball,dist_eq_norm] using hyr
      exact (min_le_left _ _).trans (hr'.trans (by nlinarith [mul_le_mul_of_nonneg_left hΓ1 hl.le]))
  exact ENNReal.ofReal_pos.mpr hc |>.trans_le H

lemma chordAngle_continuousAt {n : ℕ} (v : Space n → ℝ) {z y : Space n}
    (hy : y≠z) : ContinuousAt (chordAngle v z) y := by
  unfold chordAngle chordDirection
  exact (continuousAt_const.inner
    (((continuousAt_id.sub continuousAt_const).norm.inv₀
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))).smul
      (continuousAt_id.sub continuousAt_const))).abs

end DeGiorgi
end

end OAI
