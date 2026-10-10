import OAI.Geometry.UnitDistances.Sampling

namespace OAI

namespace PlanarUnitDistances.PowerGrowth
open Filter

def Lower {ι : Type*} (F : Filter ι) (t f : ι → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ i in F, t i ^ (a-ε) ≤ f i

def Upper {ι : Type*} (F : Filter ι) (t f : ι → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ i in F, f i ≤ t i ^ (a+ε)

variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma Lower.mono (hf : Lower F t f a) (h : f ≤ᶠ[F] g) : Lower F t g a := by
  intro ε hε
  filter_upwards [hf ε hε,h] with i hi hfg
  exact hi.trans hfg

lemma Upper.mono (hg : Upper F t g a) (h : f ≤ᶠ[F] g) : Upper F t f a := by
  intro ε hε
  filter_upwards [hg ε hε,h] with i hi hfg
  exact hfg.trans hi

lemma Lower.congr (hf : Lower F t f a) (h : f =ᶠ[F] g) : Lower F t g a :=
  hf.mono h.le

lemma Upper.congr (hf : Upper F t f a) (h : f =ᶠ[F] g) : Upper F t g a :=
  hf.mono h.symm.le

lemma eventually_one_le (ht : Tendsto t F atTop) : ∀ᶠ i in F,1 ≤ t i :=
  ht.eventually_ge_atTop 1

lemma eventually_base_pos (ht : Tendsto t F atTop) : ∀ᶠ i in F,0 < t i :=
  (eventually_one_le ht).mono fun _ hi => lt_of_lt_of_le zero_lt_one hi

lemma Lower.exponent_mono (hf : Lower F t f a) (h : b ≤ a)
    (ht : Tendsto t F atTop) : Lower F t f b := by
  intro ε hε
  filter_upwards [hf ε hε,eventually_one_le ht] with i hi hti
  exact (Real.rpow_le_rpow_of_exponent_le hti (sub_le_sub_right h ε)).trans hi

lemma Upper.exponent_mono (hf : Upper F t f a) (h : a ≤ b)
    (ht : Tendsto t F atTop) : Upper F t f b := by
  intro ε hε
  filter_upwards [hf ε hε,eventually_one_le ht] with i hi hti
  exact hi.trans (Real.rpow_le_rpow_of_exponent_le hti (by linarith))

lemma Lower.eventually_pos (hf : Lower F t f a) (ht : Tendsto t F atTop) :
    ∀ᶠ i in F,0 < f i := by
  filter_upwards [hf 1 zero_lt_one,eventually_base_pos ht] with i hi hti
  exact (Real.rpow_pos_of_pos hti _).trans_le hi

lemma Lower.mul (hf : Lower F t f a) (hg : Lower F t g b)
    (ht : Tendsto t F atTop) : Lower F t (fun i => f i*g i) (a+b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),eventually_base_pos ht]
    with i hi hj hti
  have he : a+b-ε=(a-ε/2)+(b-ε/2) := by ring
  rw [he,Real.rpow_add hti]
  exact mul_le_mul hi hj (Real.rpow_nonneg hti.le _) ((Real.rpow_nonneg hti.le _).trans hi)

lemma Upper.mul (hf : Upper F t f a) (hg : Upper F t g b)
    (hnf : ∀ᶠ i in F,0 ≤ f i) (hng : ∀ᶠ i in F,0 ≤ g i)
    (ht : Tendsto t F atTop) : Upper F t (fun i => f i*g i) (a+b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hnf,hng,eventually_base_pos ht]
    with i hi hj _ hj0 hti
  have he : a+b+ε=(a+ε/2)+(b+ε/2) := by ring
  rw [he,Real.rpow_add hti]
  exact mul_le_mul hi hj hj0 (Real.rpow_nonneg hti.le _)

lemma eventually_constant_le_rpow (ht : Tendsto t F atTop) {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ i in F,C ≤ t i ^ ε := by
  exact (_root_.tendsto_rpow_atTop hε |>.comp ht).eventually_ge_atTop C

lemma Lower.const_mul (hf : Lower F t f a) (ht : Tendsto t F atTop)
    {C : ℝ} (hC : 0 < C) : Lower F t (fun i => C*f i) a := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),eventually_constant_le_rpow ht
    (show 0<ε/2 by positivity) C⁻¹,eventually_base_pos ht] with i hi hc hti
  have hc' : 1 ≤ C*(t i)^(ε/2) := by simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hC).mp hc
  have he : a-ε/2=(a-ε)+ε/2 := by ring
  have hpos := Real.rpow_nonneg hti.le (a-ε)
  calc
    (t i)^(a-ε) ≤ (t i)^(a-ε)*(C*(t i)^(ε/2)) := le_mul_of_one_le_right hpos hc'
    _ = C*(t i)^(a-ε/2) := by
      conv_rhs => rw [he,Real.rpow_add hti]
      ring
    _ ≤ C*f i := mul_le_mul_of_nonneg_left hi hC.le

lemma Upper.const_mul (hf : Upper F t f a) (ht : Tendsto t F atTop)
    {C : ℝ} (hC : 0 ≤ C) : Upper F t (fun i => C*f i) a := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),eventually_constant_le_rpow ht
    (show 0<ε/2 by positivity) C,eventually_base_pos ht] with i hi hc hti
  have he : a+ε=ε/2+(a+ε/2) := by ring
  calc
    C*f i ≤ C*(t i)^(a+ε/2) := mul_le_mul_of_nonneg_left hi hC
    _ ≤ (t i)^(ε/2)*(t i)^(a+ε/2) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hti.le _)
    _ = (t i)^(a+ε) := by rw [he]; exact (Real.rpow_add hti _ _).symm

lemma Upper.add (hf : Upper F t f a) (hg : Upper F t g a)
    (ht : Tendsto t F atTop) : Upper F t (fun i => f i+g i) a := by
  have hmax : Upper F t (fun i => max (f i) (g i)) a := by
    intro ε hε
    filter_upwards [hf ε hε,hg ε hε] with i hi hj
    exact max_le hi hj
  exact (hmax.const_mul ht (show (0:ℝ)≤2 by norm_num)).mono
    (Eventually.of_forall fun i => by dsimp; linarith [le_max_left (f i) (g i),le_max_right (f i) (g i)])

lemma Lower.div (hf : Lower F t f a) (hg : Upper F t g b)
    (hng : ∀ᶠ i in F,0 < g i) (ht : Tendsto t F atTop) :
    Lower F t (fun i => f i/g i) (a-b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hng,eventually_base_pos ht]
    with i hi hj hj0 hti
  have he : a-b-ε=(a-ε/2)-(b+ε/2) := by ring
  rw [he,Real.rpow_sub hti]
  exact div_le_div₀ ((Real.rpow_nonneg hti.le _).trans hi) hi hj0 hj

lemma Lower.tendsto_atTop (hf : Lower F t f a) (ht : Tendsto t F atTop) (ha : 0<a) :
    Tendsto f F atTop := by
  have he : 0<a-a/2 := by linarith
  exact tendsto_atTop_mono' F (hf (a/2) (by positivity))
    ((_root_.tendsto_rpow_atTop he).comp ht)

lemma not_lower_of_upper_lt [NeBot F] (hf : Upper F t f a) (hg : Lower F t f b)
    (hab : a<b) (ht : Tendsto t F atTop) : False := by
  have hε : 0<(b-a)/3 := by linarith
  have hc : a+(b-a)/3 < b-(b-a)/3 := by linarith
  obtain ⟨i,⟨hi,hj⟩,hti⟩ := (hf _ hε |>.and (hg _ hε) |>.and
    (ht.eventually_gt_atTop 1)).exists
  have hlt := Real.rpow_lt_rpow_of_exponent_lt hti hc
  exact (not_lt_of_ge (hj.trans hi)) hlt

end PlanarUnitDistances.PowerGrowth

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma upper_rpow (ht : Tendsto t F atTop) (a : ℝ) :
    Upper F t (fun i => t i^a) a := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)
lemma lower_rpow (ht : Tendsto t F atTop) (a : ℝ) :
    Lower F t (fun i => t i^a) a := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)
lemma upper_const (ht : Tendsto t F atTop) (c : ℝ) : Upper F t (fun _ => c) 0 := by
  intro ε hε
  simpa only [zero_add] using eventually_constant_le_rpow ht hε c
lemma lower_const (ht : Tendsto t F atTop) {c : ℝ} (hc : 0<c) : Lower F t (fun _ => c) 0 := by
  have h := (lower_rpow ht 0).const_mul ht hc
  simpa only [Real.rpow_zero,mul_one] using h

lemma Upper.div (hf : Upper F t f a) (hg : Lower F t g b)
    (hng : ∀ᶠi in F,0<g i) (ht : Tendsto t F atTop) :
    Upper F t (fun i => f i/g i) (a-b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hng,eventually_base_pos ht]
    with i hi hj hj0 hti
  have he : a-b+ε=(a+ε/2)-(b-ε/2) := by ring
  rw [he,Real.rpow_sub hti]
  exact div_le_div₀ (Real.rpow_nonneg hti.le _) hi (Real.rpow_pos_of_pos hti _) hj

lemma Upper.rpow (hf : Upper F t f a) (hnf : ∀ᶠi in F,0≤f i)
    (ht : Tendsto t F atTop) {c : ℝ} (hc : 0<c) :
    Upper F t (fun i => f i^c) (a*c) := by
  intro ε hε
  filter_upwards [hf (ε/c) (div_pos hε hc),hnf,eventually_base_pos ht] with i hi hi0 hti
  have hh := Real.rpow_le_rpow hi0 hi hc.le
  rw [←Real.rpow_mul hti.le] at hh
  convert hh using 1
  congr 1
  field_simp

lemma Lower.rpow (hf : Lower F t f a) (ht : Tendsto t F atTop) {c : ℝ} (hc : 0<c) :
    Lower F t (fun i => f i^c) (a*c) := by
  intro ε hε
  filter_upwards [hf (ε/c) (div_pos hε hc),eventually_base_pos ht] with i hi hti
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hti.le _) hi hc.le
  rw [←Real.rpow_mul hti.le] at hh
  convert hh using 1
  congr 1
  field_simp

lemma Upper.tendsto_zero (hf : Upper F t f a) (hnf : ∀ᶠi in F,0≤f i)
    (ht : Tendsto t F atTop) (ha : a<0) : Tendsto f F (nhds 0) := by
  have hb := hf (-a/2) (by linarith)
  have he : a+ -a/2=a/2 := by ring
  rw [he] at hb
  have hz : Tendsto (fun x : ℝ => x^(a/2)) atTop (nhds 0) := by
    have he' : -(-a/2)=a/2 := by ring
    simpa only [he'] using (_root_.tendsto_rpow_neg_atTop (by linarith : 0 < -a/2))
  exact squeeze_zero' hnf hb (hz.comp ht)

lemma Upper.ratio_zero (hf : Upper F t f a) (hg : Lower F t g b)
    (hnf : ∀ᶠi in F,0≤f i) (ht : Tendsto t F atTop) (hab : a<b) :
    Tendsto (fun i => f i/g i) F (nhds 0) := by
  have hg0 := hg.eventually_pos ht
  exact (hf.div hg hg0 ht).tendsto_zero
    (by filter_upwards [hnf,hg0] with i hi hj; exact div_nonneg hi hj.le) ht (sub_neg.mpr hab)

lemma upper_log (ht : Tendsto t F atTop) : Upper F t (fun i => Real.log (t i)) 0 := by
  intro ε hε
  have hh := (_root_.isLittleO_log_rpow_atTop hε).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [ht.eventually hh,eventually_base_pos ht] with i hi hti
  apply (le_abs_self (Real.log (t i))).trans
  simpa only [Real.norm_eq_abs,one_mul,abs_of_nonneg (Real.rpow_nonneg hti.le ε),zero_add] using hi

lemma Upper.log (hf : Upper F t f a) (hfp : ∀ᶠi in F,0<f i)
    (ht : Tendsto t F atTop) (ha : 0≤a) : Upper F t (fun i => Real.log (f i)) 0 := by
  apply ((upper_log ht).const_mul ht (show 0≤a+1 by linarith)).mono
  filter_upwards [hf 1 zero_lt_one,hfp,eventually_base_pos ht] with i hi hfi hti
  have hh := Real.log_le_log hfi hi
  simpa only [Real.log_rpow hti] using hh

lemma Lower.of_loss (hg : Lower F t g a) {h : ι → ℝ} (hh : Upper F t h b)
    (hh0 : ∀ᶠi in F,0≤h i) (ht : Tendsto t F atTop) (hab : b<a)
    (hle : ∀ᶠi in F,g i≤f i+h i) : Lower F t f a := by
  have hlim := hh.ratio_zero hg hh0 ht hab
  have hsmall : ∀ᶠi in F,h i/g i≤1/2 := hlim.eventually_le_const (by norm_num)
  apply (hg.const_mul ht (by norm_num : (0:ℝ)<1/2)).mono
  filter_upwards [hsmall,hg.eventually_pos ht,hle] with i hi hgi hle
  have hh' := (div_le_iff₀ hgi).mp hi
  linarith

lemma diagonal {R : ℕ → ℕ → Prop} (hR : ∀k,∀ᶠn in atTop,R k n) :
    ∃f : ℕ → ℕ,Tendsto f atTop atTop ∧ ∀n,R n (f n) := by
  have h : ∀k,∃N,∀n≥N,R k n := fun k => eventually_atTop.mp (hR k)
  choose N hN using h
  refine ⟨fun n => max n (N n),tendsto_atTop_mono (fun n => le_max_left n (N n)) tendsto_id,?_⟩
  intro n
  exact hN n _ (le_max_right _ _)
end PlanarUnitDistances.PowerGrowth

namespace PlanarUnitDistances
open Filter CircleIncidence PowerGrowth
open scoped Classical
noncomputable section

lemma unordered_le_incidences (X : Finset Plane) :
    (unitPairCount X:ℝ) ≤ CircleIncidence.incidences X X := by
  have hc : unitPairCount X ≤ ((X×ˢX).filter (fun pq => dist pq.1 pq.2=1)).card := by
    unfold unitPairCount
    rw [Finset.sym2_eq_image,Finset.filter_image]
    apply Finset.card_image_le.trans
    apply le_of_eq
    congr 1
  apply (Nat.cast_le.mpr hc).trans_eq
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    Finset.sum_product,CircleIncidence.incidences,CircleIncidence.degree_sum,dist_comm]

theorem counterexample_power_sequence (hmain : ¬MainClaim) :
    ∃(t : ℕ → ℝ) (X : ℕ → Finset Plane),
      Tendsto t atTop atTop ∧ (∀i,1≤t i) ∧ (∀i,(X i).Nonempty) ∧
      (∀i,((X i).card:ℝ)=(t i)^3) ∧
      Upper atTop t (fun i => ((X i).card:ℝ)) 3 ∧
      Lower atTop t (fun i => CircleIncidence.incidences (X i) (X i)) 4 ∧
      (∀i,∀p∈X i,∀k,IsAlgebraic ℚ (p k)) := by
  obtain ⟨Y,hY⟩ := algebraic_counterexample_sequence hmain
  let X : ℕ → Finset Plane := fun i => Y (i+1)
  let t : ℕ → ℝ := fun i => ((X i).card:ℝ)^((1:ℝ)/3)
  have hcard (i : ℕ) : (i:ℝ)+1≤((X i).card:ℝ) := by
    exact_mod_cast (hY (i+1)).1
  have hcard1 (i : ℕ) : (1:ℝ)≤((X i).card:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) i,hcard i]
  have hn : Tendsto (fun i => ((X i).card:ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun i => (by linarith [hcard i] : (i:ℝ)≤((X i).card:ℝ)))
      tendsto_natCast_atTop_atTop
  have ht : Tendsto t atTop atTop := (_root_.tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp hn
  have ht1 (i : ℕ) : 1≤t i := Real.one_le_rpow (hcard1 i) (by norm_num)
  have hx0 (i : ℕ) : (X i).Nonempty := Finset.card_pos.mp (by
    have hh := (hY (i+1)).1
    dsimp [X]
    omega)
  have heq (i : ℕ) : ((X i).card:ℝ)=(t i)^3 := by
    dsimp [t]
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hu : Upper atTop t (fun i => ((X i).card:ℝ)) 3 := by
    apply (upper_rpow ht 3).congr
    exact Eventually.of_forall fun i => by simpa only [Real.rpow_ofNat] using (heq i).symm
  have hl : Lower atTop t (fun i => CircleIncidence.incidences (X i) (X i)) 4 := by
    intro ε hε
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun i:ℕ => (i:ℝ)) atTop atTop).eventually_ge_atTop (3/ε)] with i hi
    have hden : 0<(i:ℝ)+4 := by positivity
    have hinv : 1/((i:ℝ)+4)≤ε/3 := by
      apply (div_le_iff₀ hden).mpr
      have hh := (div_le_iff₀ hε).mp hi
      nlinarith
    have hexp : (1/3:ℝ)*(4-ε)≤4/3-1/((i:ℝ)+4) := by linarith
    have hp := Real.rpow_le_rpow_of_exponent_le (hcard1 i) hexp
    have hh := (hY (i+1)).2.1
    have hh' : ((X i).card:ℝ)^(4/3-1/((i:ℝ)+4)) < (unitPairCount (X i):ℝ) := by
      convert hh using 1; simp [X,Nat.cast_add]; ring_nf
    have hl' := hp.trans (hh'.le.trans (unordered_le_incidences (X i)))
    simpa only [t,←Real.rpow_mul (Nat.cast_nonneg (X i).card)] using hl'
  exact ⟨t,X,ht,ht1,hx0,heq,hu,hl,fun i => (hY (i+1)).2.2⟩
end
end PlanarUnitDistances

namespace PlanarUnitDistances.CuttingAsymptotics
open Filter PowerGrowth CircleIncidence CircleCutting
open scoped Classical
noncomputable section

lemma cuttingLog_upper {t : ℕ → ℝ} {X : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3) :
    Upper atTop t (fun i => cuttingLog (X i).card) 0 := by
  have h1 := (upper_const ht 1).exponent_mono (by norm_num : (0:ℝ)≤3) ht
  have hs := h1.add hX ht
  have hp := hs.rpow (Eventually.of_forall fun i => by positivity) ht (by norm_num : (0:ℝ)<6)
  have hp' : Upper atTop t (fun i => 81*(1+((X i).card:ℝ))^6) 18 := by
    convert hp.const_mul ht (by norm_num : (0:ℝ)≤81) using 1
    · ext i; exact congrArg (81*·) (Real.rpow_natCast (1+((X i).card:ℝ)) 6).symm
    · norm_num
  have ho := hp'.add ((upper_const ht 1).exponent_mono (by norm_num : (0:ℝ)≤18) ht) ht
  have hq := ho.const_mul ht (by norm_num : (0:ℝ)≤10)
  exact hq.log (Eventually.of_forall fun i => by positivity) ht (by norm_num)

theorem exists_cut_sequence {t : ℕ → ℝ} (X : ℕ → Finset Plane)
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1≤t i) (hX0 : ∀i,(X i).Nonempty)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hE : Lower atTop t (fun i => incidences (X i) (X i)) 4)
    {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃P Q : ℕ → Finset Plane,(∀i,P i⊆X i ∧ Q i⊆X i) ∧
      Upper atTop t (fun i => ((P i).card:ℝ)) (1+2*a) ∧
      Upper atTop t (fun i => ((Q i).card:ℝ)) (2+a) ∧
      Lower atTop t (fun i => incidences (P i) (Q i)) (2+2*a) := by
  let R : ℕ → ℝ := fun i => (t i)^(1-a)
  let B : ℕ → ℕ := fun i => Nat.ceil ((t i)^(1+2*a))+1
  have ht0 (i : ℕ) : 0<t i := zero_lt_one.trans_le (ht1 i)
  have hRp (i : ℕ) : 0<R i := Real.rpow_pos_of_pos (ht0 i) _
  have hBp (i : ℕ) : 0<B i := Nat.succ_pos _
  choose P hP Q hQ hcP hcQ hc using fun i =>
    exists_incidence_piece (X i) (X i) (hX0 i) (hRp i) (hBp i)
  have hR : Upper atTop t R (1-a) := upper_rpow ht _
  have hRl : Lower atTop t R (1-a) := lower_rpow ht _
  have hBu : Upper atTop t (fun i => (B i:ℝ)) (1+2*a) := by
    apply ((upper_rpow ht (1+2*a)).add
      ((upper_const ht 2).exponent_mono (by linarith : 0≤1+2*a) ht) ht).mono
    exact Eventually.of_forall fun i => by
      have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg (ht0 i).le (1+2*a))
      dsimp [B]
      simp only [Nat.cast_add,Nat.cast_one]
      linarith
  have hBl : Lower atTop t (fun i => (B i:ℝ)) (1+2*a) := by
    apply (lower_rpow ht (1+2*a)).mono
    exact Eventually.of_forall fun i => by
      have hh := Nat.le_ceil ((t i)^(1+2*a))
      dsimp [B]
      simp only [Nat.cast_add,Nat.cast_one]
      linarith
  have hPu : Upper atTop t (fun i => ((P i).card:ℝ)) (1+2*a) :=
    hBu.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (hcP i))
  have hQu : Upper atTop t (fun i => ((Q i).card:ℝ)) (2+a) := by
    have hh := (hX.div hRl (Eventually.of_forall hRp) ht).mono (Eventually.of_forall hcQ)
    convert hh using 1; ring
  let S : ℕ → ℝ := fun i => R i*cuttingLog (X i).card+1
  have hln := cuttingLog_upper ht hX
  have hSu : Upper atTop t S (1-a) := by
    have hh := hR.mul hln (Eventually.of_forall fun i => (hRp i).le)
      (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _)) ht
    simp only [add_zero] at hh
    exact hh.add ((upper_const ht 1).exponent_mono (by linarith : 0≤1-a) ht) ht
  have hS0 (i : ℕ) : 0≤S i := by
    dsimp [S]
    exact add_nonneg (mul_nonneg (hRp i).le (zero_le_one.trans (cuttingLog_one_le _))) zero_le_one
  let K : ℕ → ℝ := fun i => 43*(1+(S i)^2)+((X i).card:ℝ)/(B i:ℝ)
  have hKp (i : ℕ) : 0<K i := by dsimp [K]; positivity
  have hKu : Upper atTop t K (2-2*a) := by
    have hs2 := hSu.mul hSu (Eventually.of_forall hS0) (Eventually.of_forall hS0) ht
    have hs2' : Upper atTop t (fun i => (S i)^2) (2-2*a) := by
      convert hs2 using 1 <;> ring_nf
    have hu := ((upper_const ht 1).exponent_mono (by linarith : 0≤2-2*a) ht).add hs2' ht
    have hv := hX.div hBl (Eventually.of_forall fun i => Nat.cast_pos.mpr (hBp i)) ht
    have hv' : Upper atTop t (fun i => ((X i).card:ℝ)/(B i:ℝ)) (2-2*a) := by
      convert hv using 1; ring
    exact (hu.const_mul ht (by norm_num : (0:ℝ)≤43)).add hv' ht
  let loss : ℕ → ℝ := fun i => S i*(((X i).card:ℝ)+2*(X i).card)
  have hlu : Upper atTop t loss (4-a) := by
    have hn := hX.add (hX.const_mul ht (by norm_num : (0:ℝ)≤2)) ht
    have hh := hSu.mul hn (Eventually.of_forall hS0)
      (Eventually.of_forall fun i => by positivity) ht
    convert hh using 1; ring
  have hkeep : Lower atTop t (fun i => K i*incidences (P i) (Q i)) 4 :=
    hE.of_loss hlu (Eventually.of_forall fun i => mul_nonneg (hS0 i) (by positivity)) ht
      (by linarith) (Eventually.of_forall fun i => by
        have hh := hc i
        change incidences (X i) (X i) ≤ loss i+K i*incidences (P i) (Q i) at hh
        linarith)
  have hfinal := hkeep.div hKu (Eventually.of_forall hKp) ht
  have hfinal' : Lower atTop t (fun i => incidences (P i) (Q i)) (2+2*a) := by
    have he : (fun i => K i*incidences (P i) (Q i)/K i) =
        (fun i => incidences (P i) (Q i)) := by
      funext i
      exact mul_div_cancel_left₀ _ (hKp i).ne'
    rw [he] at hfinal
    convert hfinal using 1; ring
  exact ⟨P,Q,fun i => ⟨hP i,hQ i⟩,hPu,hQu,hfinal'⟩
end
end PlanarUnitDistances.CuttingAsymptotics

namespace PlanarUnitDistances.CircleIncidence
open Finset CircleCutting
open scoped Classical
noncomputable section

lemma high_degree_card (P Q : Finset Plane) {a : ℝ} (ha : 0 < a) :
    ((Q.filter (fun q => a < degree P q)).card : ℝ) ≤ incidences P Q/a := by
  apply (le_div_iff₀ ha).mpr
  have hh : ((Q.filter (fun q => a < degree P q)).card : ℝ)*a ≤ ∑q ∈ Q.filter (fun q => a < degree P q),degree P q := by
    calc
      _ = ∑q ∈ Q.filter (fun q => a < degree P q),a := by simp
      _ ≤ _ := Finset.sum_le_sum (fun q hq => (Finset.mem_filter.mp hq).2.le)
  exact hh.trans (incidences_mono_right P (Finset.filter_subset _ _))

lemma incidence_bound_enlarged (P Q : Finset Plane) {L m n : ℝ}
    (hL : 1 ≤ L) (hlP : cuttingLog P.card ≤ L) (hlQ : cuttingLog Q.card ≤ L)
    (hm : (P.card : ℝ) ≤ m) (hn : (Q.card : ℝ) ≤ n) :
    incidences P Q ≤ 1000*L^2*((m*n)^((2:ℝ)/3)+m+n) := by
  have h0 := (Nat.cast_nonneg P.card : (0:ℝ) ≤ P.card)
  have h1 := (Nat.cast_nonneg Q.card : (0:ℝ) ≤ Q.card)
  have hi : incidences P Q ≤ 1000*L^2*(((P.card:ℝ)*Q.card)^((2:ℝ)/3)+P.card+Q.card) := by
    rcases le_total P.card Q.card with h | h
    · exact incidence_bound_oriented P Q h hL hlQ
    · have he := incidence_bound_oriented Q P h hL hlP
      rw [incidences_comm Q P] at he
      convert he using 1; ring_nf
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp := Real.rpow_le_rpow (mul_nonneg h0 h1)
    (mul_le_mul hm hn h1 (h0.trans hm)) (by norm_num : (0:ℝ) ≤ 2/3)
  linarith

theorem exists_trimmed (P Q : Finset Plane) {a b L : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hL : 1 ≤ L)
    (hlP : cuttingLog P.card ≤ L) (hlQ : cuttingLog Q.card ≤ L) :
    ∃F ⊆ P,∃G ⊆ Q,
      (∀p∈F,degree G p ≤ a) ∧ (∀q∈G,degree F q ≤ b) ∧
      incidences P Q ≤ incidences F G+
        1000*L^2*((incidences P Q/a*(Q.card:ℝ))^((2:ℝ)/3)+incidences P Q/a+Q.card)+
        1000*L^2*(((P.card:ℝ)*(incidences P Q/b))^((2:ℝ)/3)+P.card+incidences P Q/b) := by
  let F := P.filter (fun p => degree Q p ≤ a)
  let G := Q.filter (fun q => degree P q ≤ b)
  let H := P.filter (fun p => a < degree Q p)
  let J := Q.filter (fun q => b < degree P q)
  have hF : F⊆P := Finset.filter_subset _ _
  have hG : G⊆Q := Finset.filter_subset _ _
  have hH : H⊆P := Finset.filter_subset _ _
  have hJ : J⊆Q := Finset.filter_subset _ _
  have hcH : (H.card:ℝ) ≤ incidences P Q/a := by
    simpa only [incidences_comm Q P] using high_degree_card Q P ha
  have hcJ : (J.card:ℝ) ≤ incidences P Q/b := high_degree_card P Q hb
  have hHP : cuttingLog H.card ≤ L := (cuttingLog_mono (Finset.card_le_card hH)).trans hlP
  have hJQ : cuttingLog J.card ≤ L := (cuttingLog_mono (Finset.card_le_card hJ)).trans hlQ
  have heH := incidence_bound_enlarged H Q hL hHP hlQ hcH (le_refl (Q.card:ℝ))
  have heJ := incidence_bound_enlarged P J hL hlP hJQ (le_refl (P.card:ℝ)) hcJ
  have hs1 : incidences P Q=incidences F Q+incidences H Q := by
    simpa only [not_le] using incidences_filter_split P Q (fun p => degree Q p ≤ a)
  have hs2 : incidences F Q=incidences F G+incidences F J := by
    have hh := incidences_filter_split Q F (fun q => degree P q ≤ b)
    have hh' : incidences Q F=incidences G F+incidences J F := by
      simpa only [not_le] using hh
    simpa only [incidences_comm Q F,incidences_comm G F,incidences_comm J F] using hh'
  have hfj := incidences_mono_left hF J
  refine ⟨F,hF,G,hG,?_,?_,?_⟩
  · intro p hp
    exact (degree_mono hG p).trans (Finset.mem_filter.mp hp).2
  · intro q hq
    exact (degree_mono hF q).trans (Finset.mem_filter.mp hq).2
  · linarith
end
end PlanarUnitDistances.CircleIncidence

namespace PlanarUnitDistances.CuttingAsymptotics
open Filter PowerGrowth CircleIncidence CircleCutting
open scoped Classical
noncomputable section

lemma incidence_upper {t : ℕ → ℝ} {X P Q : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hPX : ∀i,P i⊆X i) (hQX : ∀i,Q i⊆X i)
    {m n e : ℝ} (hP : Upper atTop t (fun i => ((P i).card:ℝ)) m)
    (hQ : Upper atTop t (fun i => ((Q i).card:ℝ)) n)
    (hm : m≤e) (hn : n≤e) (hmn : (m+n)*(2/3:ℝ)≤e) :
    Upper atTop t (fun i => incidences (P i) (Q i)) e := by
  have hlog := cuttingLog_upper ht hX
  have hLp := hlog.mul hlog
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _))
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _)) ht
  have hL : Upper atTop t (fun i => 1000*(cuttingLog (X i).card)^2) 0 := by
    have hh := hLp.const_mul ht (by norm_num : (0:ℝ)≤1000)
    convert hh using 1 <;> ring_nf
  have hprod := hP.mul hQ (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht
  have hmixed := (hprod.rpow (Eventually.of_forall fun i => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ht (by norm_num : (0:ℝ)<2/3)).exponent_mono hmn ht
  have hsum := (hmixed.add (hP.exponent_mono hm ht) ht).add (hQ.exponent_mono hn ht) ht
  have htot := hL.mul hsum (Eventually.of_forall fun i => by positivity)
    (Eventually.of_forall fun i => by positivity) ht
  simp only [zero_add] at htot
  apply htot.mono
  exact Eventually.of_forall fun i => incidence_bound_enlarged (P i) (Q i)
    (cuttingLog_one_le _) (cuttingLog_mono (Finset.card_le_card (hPX i)))
      (cuttingLog_mono (Finset.card_le_card (hQX i))) le_rfl le_rfl

theorem trim_sequence {t : ℕ → ℝ} {X P Q : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1≤t i)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hPX : ∀i,P i⊆X i) (hQX : ∀i,Q i⊆X i)
    {a b : ℝ} (_ha : 0<a) (ha1 : a<1) (hb : 0<b) (hba : b<a)
    (hP : Upper atTop t (fun i => ((P i).card:ℝ)) (1+2*a))
    (hQ : Upper atTop t (fun i => ((Q i).card:ℝ)) (2+a))
    (hE : Lower atTop t (fun i => incidences (P i) (Q i)) (2+2*a)) :
    ∃F G : ℕ → Finset Plane,(∀i,F i⊆P i ∧ G i⊆Q i) ∧
      (∀i,∀p∈F i,degree (G i) p≤(t i)^(1+b)) ∧
      (∀i,∀q∈G i,degree (F i) q≤(t i)^(a+b)) ∧
      Upper atTop t (fun i => ((F i).card:ℝ)) (1+2*a) ∧
      Upper atTop t (fun i => ((G i).card:ℝ)) (2+a) ∧
      Lower atTop t (fun i => incidences (F i) (G i)) (2+2*a) := by
  have ht0 (i : ℕ) : 0<t i := zero_lt_one.trans_le (ht1 i)
  let L : ℕ → ℝ := fun i => cuttingLog (X i).card
  let A : ℕ → ℝ := fun i => (t i)^(1+b)
  let B : ℕ → ℝ := fun i => (t i)^(a+b)
  have hAp (i : ℕ) : 0<A i := Real.rpow_pos_of_pos (ht0 i) _
  have hBp (i : ℕ) : 0<B i := Real.rpow_pos_of_pos (ht0 i) _
  choose F hF G hG hdF hdG he using fun i => exists_trimmed (P i) (Q i)
    (hAp i) (hBp i) (cuttingLog_one_le (X i).card)
    (cuttingLog_mono (Finset.card_le_card (hPX i))) (cuttingLog_mono (Finset.card_le_card (hQX i)))
  have hEu : Upper atTop t (fun i => incidences (P i) (Q i)) (2+2*a) :=
    incidence_upper ht hX hPX hQX hP hQ (by linarith) (by linarith) (by ring_nf; rfl)
  have hlog := cuttingLog_upper ht hX
  have hLp := hlog.mul hlog
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _))
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _)) ht
  have hLu : Upper atTop t (fun i => 1000*(L i)^2) 0 := by
    dsimp only [L]
    have hh := hLp.const_mul ht (by norm_num : (0:ℝ)≤1000)
    convert hh using 1 <;> ring_nf
  have hEA := hEu.div (lower_rpow ht (1+b)) (Eventually.of_forall hAp) ht
  have hEB := hEu.div (lower_rpow ht (a+b)) (Eventually.of_forall hBp) ht
  have hEA0 : ∀ᶠi in atTop,0≤ incidences (P i) (Q i)/A i :=
    Eventually.of_forall fun i => div_nonneg (incidences_nonneg _ _) (hAp i).le
  have hEB0 : ∀ᶠi in atTop,0≤ incidences (P i) (Q i)/B i :=
    Eventually.of_forall fun i => div_nonneg (incidences_nonneg _ _) (hBp i).le
  have hPA := hEA.mul hQ hEA0 (Eventually.of_forall fun i => Nat.cast_nonneg _) ht
  have hPB := hP.mul hEB (Eventually.of_forall fun i => Nat.cast_nonneg _) hEB0 ht
  have hPA0 : ∀ᶠi in atTop,0≤ incidences (P i) (Q i)/A i*((Q i).card:ℝ) :=
    hEA0.mono fun i hi => mul_nonneg hi (Nat.cast_nonneg _)
  have hPB0 : ∀ᶠi in atTop,0≤((P i).card:ℝ)*(incidences (P i) (Q i)/B i) :=
    hEB0.mono fun i hi => mul_nonneg (Nat.cast_nonneg _) hi
  have hMA := (hPA.rpow hPA0 ht (by norm_num : (0:ℝ)<2/3)).exponent_mono
    (show ((2+2*a-(1+b))+(2+a))*(2/3:ℝ)≤2+2*a-b/2 by linarith) ht
  have hMB := (hPB.rpow hPB0 ht (by norm_num : (0:ℝ)<2/3)).exponent_mono
    (show ((1+2*a)+(2+2*a-(a+b)))*(2/3:ℝ)≤2+2*a-b/2 by linarith) ht
  have hSA := (hMA.add (hEA.exponent_mono (by linarith : 2+2*a-(1+b)≤2+2*a-b/2) ht) ht).add
    (hQ.exponent_mono (by linarith : 2+a≤2+2*a-b/2) ht) ht
  have hSB := (hMB.add (hP.exponent_mono (by linarith : 1+2*a≤2+2*a-b/2) ht) ht).add
    (hEB.exponent_mono (by linarith : 2+2*a-(a+b)≤2+2*a-b/2) ht) ht
  have hA0 : ∀ᶠi in atTop,0≤(incidences (P i) (Q i)/A i*((Q i).card:ℝ))^(2/3:ℝ)+incidences (P i) (Q i)/A i+(Q i).card := by
    filter_upwards [hEA0] with i hi
    positivity
  have hB0 : ∀ᶠi in atTop,0≤(((P i).card:ℝ)*(incidences (P i) (Q i)/B i))^(2/3:ℝ)+(P i).card+incidences (P i) (Q i)/B i := by
    filter_upwards [hEB0] with i hi
    positivity
  have hLA := hLu.mul hSA (Eventually.of_forall fun i => by positivity) hA0 ht
  have hLB := hLu.mul hSB (Eventually.of_forall fun i => by positivity) hB0 ht
  simp only [zero_add] at hLA hLB
  have hloss := hLA.add hLB ht
  have hnon : ∀ᶠi in atTop,0≤1000*(L i)^2*((incidences (P i) (Q i)/A i*((Q i).card:ℝ))^(2/3:ℝ)+incidences (P i) (Q i)/A i+(Q i).card)+
      1000*(L i)^2*((((P i).card:ℝ)*(incidences (P i) (Q i)/B i))^(2/3:ℝ)+(P i).card+incidences (P i) (Q i)/B i) := by
    filter_upwards [hA0,hB0] with i hi hj
    positivity
  refine ⟨F,G,fun i => ⟨hF i,hG i⟩,hdF,hdG,
    hP.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (Finset.card_le_card (hF i))),
    hQ.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (Finset.card_le_card (hG i))),?_⟩
  apply hE.of_loss hloss hnon ht (by linarith)
  exact Eventually.of_forall fun i => by simpa only [add_assoc] using he i
end
end PlanarUnitDistances.CuttingAsymptotics

end OAI
