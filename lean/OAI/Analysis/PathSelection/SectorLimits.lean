import Mathlib
import OAI.Analysis.PathSelection.SectorBounds

namespace OAI

/-! Sector filters, subexponential estimates and grouped leading coefficients. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees

def sectorInfinity : Filter ℂ where
  sets := {s | SectorEventually (fun z => z ∈ s)}
  univ_sets := SectorEventually.truth
  sets_of_superset := fun h hs => h.mono (fun _ hz => hs hz)
  inter_sets := fun h k => h.and k

lemma eventually_sectorInfinity {P : ℂ → Prop} :
    (∀ᶠ z in sectorInfinity, P z) ↔ SectorEventually P := Iff.rfl

instance sectorInfinity_neBot : NeBot sectorInfinity := by
  refine ⟨?_⟩
  intro h
  have hem : (∅ : Set ℂ) ∈ sectorInfinity := by rw [h]; simp
  obtain ⟨ω,R,hω,hbad⟩ := hem
  obtain ⟨t,ht⟩ := (hω.real_discs R).exists
  exact hbad (t:ℂ) (ht.2 (Metric.mem_closedBall_self (by linarith [ht.1])))

lemma tendsto_norm_sectorInfinity : Tendsto (norm : ℂ → ℝ) sectorInfinity atTop := by
  apply Filter.tendsto_atTop.mpr
  intro R
  apply SectorEventually.of_radial
  filter_upwards [eventually_ge_atTop R] with r hr
  intro z hz
  simpa only [hz] using hr

lemma tendsto_real_sectorInfinity : Tendsto (fun t : ℝ => (t:ℂ)) atTop sectorInfinity := by
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨ω,R,hω,h⟩ := hs
  filter_upwards [hω.real_discs R] with t ht
  exact h (t:ℂ) (ht.2 (Metric.mem_closedBall_self (by linarith [ht.1])))

lemma tendsto_re_sectorInfinity : Tendsto Complex.re sectorInfinity atTop := by
  apply Filter.tendsto_atTop.mpr
  intro A
  have hg := (isLittleO_log_rpow_rpow_atTop (s := (1:ℝ)) 2 zero_lt_one).bound
    (show (0:ℝ) < (2*(max A 0+1))⁻¹ by positivity)
  have hdata : ∀ᶠ r : ℝ in atTop,
      0 ≤ baseLoss r ∧ baseLoss r ≤ Real.pi/2 ∧ 2*A ≤ r*baseLoss r := by
    filter_upwards [hg,admissible_baseLoss.1,
      admissible_baseLoss.tendsto_zero.eventually (gt_mem_nhds (show (0:ℝ)<Real.pi/2 by positivity)),
      eventually_gt_atTop (1:ℝ)] with r hr hloss hpi hr1
    have hr0 : 0<r := zero_lt_one.trans hr1
    have hl : 0<Real.log r := Real.log_pos hr1
    have hc : 0<2*(max A 0+1) := by positivity
    have hh : (Real.log r)^2 ≤ (2*(max A 0+1))⁻¹*r := by
      simpa only [Real.rpow_two,Real.rpow_one,Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (Real.log r)),abs_of_pos hr0] using hr
    refine ⟨hloss.1.le,hpi.le,?_⟩
    dsimp [baseLoss]
    rw [inv_pow,←div_eq_mul_inv,(le_div_iff₀ (sq_pos_of_pos hl))]
    have hh' := mul_le_mul_of_nonneg_left hh hc.le
    have he : (2*(max A 0+1))*((2*(max A 0+1))⁻¹*r)=r := by field_simp
    rw [he] at hh'
    nlinarith [le_max_left A 0,sq_nonneg (Real.log r)]
  obtain ⟨T,hT⟩ := eventually_atTop.mp hdata
  exact ⟨baseLoss,T,admissible_baseLoss,fun z hz => by
    have ht := hT ‖z‖ hz.1.le
    have hr := half_loss_norm_le_re ht.1 ht.2.1 hz.2
    change A ≤ z.re
    calc
      A = (2*A)/2 := by ring
      _ ≤ (‖z‖*baseLoss ‖z‖)/2 := div_le_div_of_nonneg_right ht.2.2 (by norm_num)
      _ = baseLoss ‖z‖/2*‖z‖ := by ring
      _ ≤ z.re := hr⟩

namespace Clock

def ExpBound (a : ℝ) (f : ℂ → ℂ) : Prop :=
  f =O[sectorInfinity] (fun z => Real.exp (a*z.re))

def ExpSmall (B : ℝ) (f : ℂ → ℂ) : Prop := ∃ a < B, ExpBound a f

def SectorSlow (f : ℂ → ℂ) : Prop := ∀ ε : ℝ, 0 < ε → ExpBound ε f

lemma ExpBound.mono {a b : ℝ} {f : ℂ → ℂ} (h : ExpBound a f) (hab : a ≤ b) :
    ExpBound b f := by
  apply h.trans
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [show ∀ᶠ z in sectorInfinity, 0 < z.re from SectorEventually.realpart_pos] with z hz
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul] using
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hz.le)

lemma ExpBound.mul {a b : ℝ} {f g : ℂ → ℂ} (hf : ExpBound a f) (hg : ExpBound b g) :
    ExpBound (a+b) (fun z => f z*g z) := by
  simpa only [ExpBound,←Real.exp_add,←add_mul] using Asymptotics.IsBigO.mul hf hg

lemma ExpBound.add {a : ℝ} {f g : ℂ → ℂ} (hf : ExpBound a f) (hg : ExpBound a g) :
    ExpBound a (fun z => f z+g z) := Asymptotics.IsBigO.add hf hg

lemma ExpSmall.mono {a b : ℝ} {f : ℂ → ℂ} (hf : ExpSmall a f) (hab : a ≤ b) :
    ExpSmall b f := by
  obtain ⟨c,hc,h⟩ := hf
  exact ⟨c,hc.trans_le hab,h⟩

lemma ExpSmall.add {a : ℝ} {f g : ℂ → ℂ} (hf : ExpSmall a f) (hg : ExpSmall a g) :
    ExpSmall a (fun z => f z+g z) := by
  obtain ⟨b,hb,hf⟩ := hf
  obtain ⟨c,hc,hg⟩ := hg
  exact ⟨max b c,max_lt hb hc,(hf.mono (le_max_left _ _)).add (hg.mono (le_max_right _ _))⟩

lemma ExpSmall.mul {a b : ℝ} {f g : ℂ → ℂ} (hf : ExpSmall a f) (hg : ExpBound b g) :
    ExpSmall (a+b) (fun z => f z*g z) := by
  obtain ⟨c,hc,hf⟩ := hf
  exact ⟨c+b,by linarith,hf.mul hg⟩

end Clock
end DegeneratingTrees

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees

 
def Subexponential {α : Type*} (l : Filter α) (X : α → ℝ) (a : α → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ‖a x‖ ≤ Real.exp (ε*X x)

lemma log_div_tendsto_zero {α : Type*} {l : Filter α} {X : α → ℝ}
    (hX : Tendsto X l atTop) :
    Tendsto (fun x => Real.log (X x)/X x) l (𝓝 0) := by
  simpa only [Function.comp_apply, id_eq] using! Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hX

lemma exponent_ratio_zero {α : Type*} {l : Filter α} {X M : α → ℝ}
    (hX : Tendsto X l atTop) (hM : Tendsto (fun x => M x/X x) l (𝓝 0))
    (C : ℝ) :
    Tendsto (fun x => (C*(1+M x)+C*Real.log (X x))/X x) l (𝓝 0) := by
  have hi : Tendsto (fun x => (X x)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hX
  have ht := ((hi.add hM).const_mul C).add
    ((log_div_tendsto_zero hX).const_mul C)
  simp only [add_zero,mul_zero] at ht
  convert ht using 1
  funext x
  ring

 

theorem subexponential_of_lower_size_bound {α : Type*} {l : Filter α}
    {X M : α → ℝ} {a : α → ℂ} (hX : Tendsto X l atTop)
    (hM : Tendsto (fun x => M x/X x) l (𝓝 0))
    (C : ℝ) (ha : ∀ᶠ x in l,
      ‖a x‖ ≤ Real.exp (C*(1+M x))*(X x)^C) : Subexponential l X a := by
  intro ε hε
  have he := (exponent_ratio_zero hX hM C).eventually_lt_const hε
  filter_upwards [ha,he,hX.eventually_gt_atTop 0] with x hx hex hp
  apply hx.trans
  rw [Real.rpow_def_of_pos hp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he' := (div_lt_iff₀ hp).mp hex
  nlinarith

 

theorem negative_exponential_times_subexponential {α : Type*} {l : Filter α}
    {X : α → ℝ} {a : α → ℂ} (hX : Tendsto X l atTop)
    (ha : Subexponential l X a) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x => Real.exp (-ε*X x)*‖a x‖) l (𝓝 0) := by
  have he : Tendsto (fun x => Real.exp (-(ε/2)*X x)) l (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_const_mul_atBot_of_neg (show -(ε/2) < 0 by linarith)).mpr hX
  apply squeeze_zero' (Eventually.of_forall (fun x => by positivity)) _ he
  filter_upwards [ha (ε/2) (by linarith)] with x hx
  calc
    Real.exp (-ε*X x)*‖a x‖ ≤ Real.exp (-ε*X x)*Real.exp ((ε/2)*X x) :=
      mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
    _ = Real.exp (-(ε/2)*X x) := by rw [←Real.exp_add]; congr 1; ring

lemma Subexponential.const {α : Type*} {l : Filter α} {X : α → ℝ}
    (hX : Tendsto X l atTop) (c : ℂ) : Subexponential l X (fun _ => c) := by
  intro ε hε
  have he : Tendsto (fun x => Real.exp (ε*X x)) l atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_const_mul_atTop_of_pos hε).mpr hX)
  exact he.eventually_ge_atTop ‖c‖

lemma Subexponential.mul {α : Type*} {l : Filter α} {X : α → ℝ} {a b : α → ℂ}
    (ha : Subexponential l X a) (hb : Subexponential l X b) :
    Subexponential l X (fun x => a x*b x) := by
  intro ε hε
  filter_upwards [ha (ε/2) (by linarith),hb (ε/2) (by linarith)] with x hx hy
  rw [norm_mul]
  calc
    ‖a x‖*‖b x‖ ≤ Real.exp ((ε/2)*X x)*Real.exp ((ε/2)*X x) :=
      mul_le_mul hx hy (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (ε*X x) := by rw [←Real.exp_add]; congr 1; ring

end DegeneratingTrees

 

 

 

open Set Filter Topology Complex
open scoped BigOperators
namespace DegeneratingTrees

 

theorem exists_first_coefficient {α E : Type*} [Zero E] {l : Filter α}
    (D : Set ℝ) (hD : ∀ B : ℝ, (D ∩ Iic B).Finite)
    (b : ℝ → α → E) (hne : ∃ d ∈ D, ¬ b d =ᶠ[l] fun _ => 0) :
    ∃ d ∈ D, (¬ b d =ᶠ[l] fun _ => 0) ∧
      ∀ e ∈ D, e < d → b e =ᶠ[l] fun _ => 0 := by
  classical
  obtain ⟨a,ha,hba⟩ := hne
  let S : Finset ℝ := ((hD a).toFinset).filter fun d => ¬ b d =ᶠ[l] fun _ => 0
  have haS : a ∈ S := by simp [S,ha,hba]
  let d := S.min' ⟨a,haS⟩
  have hd : d ∈ S := Finset.min'_mem _ _
  have hdD : d ∈ D := ((hD a).mem_toFinset.mp (Finset.mem_filter.mp hd).1).1
  have hda : d ≤ a := Finset.min'_le _ _ haS
  refine ⟨d,hdD,(Finset.mem_filter.mp hd).2,?_⟩
  intro e he hed
  by_contra hbe
  have heS : e ∈ S := by
    simp only [S,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_inter_iff,Set.mem_Iic]
    exact ⟨⟨he,hed.le.trans hda⟩,hbe⟩
  exact (not_le_of_gt hed) (Finset.min'_le _ _ heS)

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {l : Filter α} {X : α → ℝ}

 

lemma normalized_grouped_error {F b : α → E} {k : α → ℂ} {d ε C : ℝ}
    (hX : Tendsto X l atTop) (hk : Subexponential l X (fun x => (k x)⁻¹))
    (hε : 0 < ε) (hC : 0 ≤ C)
    (herr : ∀ᶠ x in l, ‖F x-(Real.exp (-d*X x):ℂ) • b x‖ ≤
      C*Real.exp (-(d+ε)*X x)) :
    Tendsto (fun x => ((Real.exp (d*X x):ℂ)*(k x)⁻¹) •
      (F x-(Real.exp (-d*X x):ℂ) • b x)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (negative_exponential_times_subexponential hX hk hε).const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _)) _ ht
  filter_upwards [herr] with x hx
  rw [norm_smul,norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le]
  calc
    Real.exp (d*X x)*‖(k x)⁻¹‖*‖F x-(Real.exp (-d*X x):ℂ) • b x‖ ≤
        Real.exp (d*X x)*‖(k x)⁻¹‖*(C*Real.exp (-(d+ε)*X x)) :=
      mul_le_mul_of_nonneg le_rfl hx (by positivity) (mul_nonneg hC (Real.exp_pos _).le)
    _ = C*(Real.exp (-ε*X x)*‖(k x)⁻¹‖) := by
      have he : Real.exp (d*X x)*Real.exp (-(d+ε)*X x) = Real.exp (-ε*X x) := by
        rw [←Real.exp_add]; congr 1; ring
      calc
        _ = C*(Real.exp (d*X x)*Real.exp (-(d+ε)*X x))*‖(k x)⁻¹‖ := by ring
        _ = _ := by rw [he]; ring

 

theorem grouped_leading_normalization {F b : α → E} {k : α → ℂ} {d ε C : ℝ}
    (hX : Tendsto X l atTop) (hk : Subexponential l X (fun x => (k x)⁻¹))
    (hε : 0 < ε) (hC : 0 ≤ C)
    (herr : ∀ᶠ x in l, ‖F x-(Real.exp (-d*X x):ℂ) • b x‖ ≤
      C*Real.exp (-(d+ε)*X x))
    {g : E} (hb : Tendsto (fun x => (k x)⁻¹ • b x) l (𝓝 g)) :
    Tendsto (fun x => ((Real.exp (d*X x):ℂ)*(k x)⁻¹) • F x) l (𝓝 g) := by
  have he := normalized_grouped_error hX hk hε hC herr
  have heq : (fun x => ((Real.exp (d*X x):ℂ)*(k x)⁻¹) •
      (F x-(Real.exp (-d*X x):ℂ) • b x) + (k x)⁻¹ • b x) =
      (fun x => ((Real.exp (d*X x):ℂ)*(k x)⁻¹) • F x) := by
    funext x
    rw [smul_sub,smul_smul]
    have hexp : (Real.exp (d*X x):ℂ)*(k x)⁻¹*(Real.exp (-d*X x):ℂ) = (k x)⁻¹ := by
      rw [mul_right_comm,←Complex.ofReal_mul,←Real.exp_add]
      simp
    rw [hexp]
    abel
  simpa only [zero_add,heq] using he.add hb

 

theorem grouped_normalization_or_zero_coefficients
    (D : Set ℝ) (hD : ∀ B : ℝ, (D ∩ Iic B).Finite)
    (b : ℝ → α → E) (F : α → E) (hX : Tendsto X l atTop)
    (hnorm : ∀ d ∈ D, (¬ b d =ᶠ[l] fun _ => 0) →
      ∃ k : α → ℂ, Subexponential l X (fun x => (k x)⁻¹) ∧
        ∃ g : E, g ≠ 0 ∧ Tendsto (fun x => (k x)⁻¹ • b d x) l (𝓝 g))
    (hrem : ∀ B ∈ D, ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ᶠ x in l, ‖F x - ∑ d ∈ (hD B).toFinset,
        (Real.exp (-d*X x):ℂ) • b d x‖ ≤ C*Real.exp (-(B+ε)*X x)) :
    (∀ d ∈ D, b d =ᶠ[l] fun _ => 0) ∨
    (∃ d ∈ D, ∃ k : α → ℂ, ∃ g : E, g ≠ 0 ∧
      Tendsto (fun x => ((Real.exp (d*X x):ℂ)*(k x)⁻¹) • F x) l (𝓝 g)) := by
  classical
  by_cases hz : ∀ d ∈ D, b d =ᶠ[l] fun _ => 0
  · exact Or.inl hz
  right
  have hex : ∃ d ∈ D, ¬ b d =ᶠ[l] fun _ => 0 := by simpa using hz
  obtain ⟨d,hd,hbd,hfirst⟩ := exists_first_coefficient D hD b hex
  obtain ⟨k,hk,g,hg,hbg⟩ := hnorm d hd hbd
  obtain ⟨ε,C,hε,hC,herr⟩ := hrem d hd
  have hearly : ∀ᶠ x in l, ∀ e ∈ (hD d).toFinset, e ≠ d → b e x = 0 := by
    rw [Filter.eventually_all_finset]
    intro e he
    by_cases heq : e = d
    · exact Eventually.of_forall (fun _ hne => (hne heq).elim)
    · have hed := (hD d).mem_toFinset.mp he
      exact (hfirst e hed.1 (lt_of_le_of_ne hed.2 heq)).mono fun x hx _ => hx
  refine ⟨d,hd,k,g,hg,grouped_leading_normalization hX hk hε hC ?_ hbg⟩
  filter_upwards [herr,hearly] with x hx he
  have hsum : (∑ e ∈ (hD d).toFinset, (Real.exp (-e*X x):ℂ) • b e x) =
      (Real.exp (-d*X x):ℂ) • b d x := by
    apply Finset.sum_eq_single d
    · intro e heS hed
      rw [he e heS hed,smul_zero]
    · intro hdS
      exact (hdS ((hD d).mem_toFinset.mpr ⟨hd,by simpa only [Set.mem_Iic] using le_refl d⟩)).elim
  simpa only [hsum] using hx

end DegeneratingTrees
end

end OAI
