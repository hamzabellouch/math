import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open Set Real
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def optionSupport [DecidableEq ι] (f : ι → Option κ) : Finset ι :=
  Finset.univ.filter (fun i => (f i).isSome)

omit [Fintype κ] in
lemma option_support_weight [DecidableEq ι] (h : ℝ) (f : ι → Option κ) :
    (∏ i, if (f i).isSome then h else 1) = h^(optionSupport f).card := by
  rw [← Finset.prod_filter]
  simp [optionSupport]

lemma option_weight_sum [DecidableEq ι] (h : ℝ) :
    (∑ f : ι → Option κ, h^(optionSupport f).card)=(1+(Fintype.card κ:ℝ)*h)^(Fintype.card ι) := by
  simp only [← option_support_weight]
  rw [← Fintype.prod_sum (fun (_ : ι) (o : Option κ) => if o.isSome then h else 1)]
  simp [Fintype.sum_option]

theorem sparse_option_count [DecidableEq ι] [DecidableEq κ]
    {h α : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (s : Finset (ι → Option κ))
    (hs : ∀ f ∈ s, ((optionSupport f).card:ℝ) ≤ α*(Fintype.card ι:ℝ)) :
    (s.card:ℝ) ≤ exp (((Fintype.card κ:ℝ)*h-α*log h)*(Fintype.card ι:ℝ)) := by
  have hb : (s.card:ℝ)*exp (α*(Fintype.card ι:ℝ)*log h) ≤
      (1+(Fintype.card κ:ℝ)*h)^(Fintype.card ι) := by
    calc
      _ = ∑ _f ∈ s, exp (α*(Fintype.card ι:ℝ)*log h) := by simp
      _ ≤ ∑ f ∈ s, h^(optionSupport f).card := by
        apply Finset.sum_le_sum
        intro f hf
        rw [mul_comm (α*(Fintype.card ι:ℝ)) (log h),← Real.rpow_def_of_pos hh,← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (hs f hf)
      _ ≤ ∑ f : ι → Option κ, h^(optionSupport f).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => pow_nonneg hh.le _)
      _ = _ := option_weight_sum h
  have ht : 0 < 1+(Fintype.card κ:ℝ)*h := by positivity
  have he : (1+(Fintype.card κ:ℝ)*h)^(Fintype.card ι) ≤
      exp ((Fintype.card ι:ℝ)*(Fintype.card κ:ℝ)*h) := by
    rw [← Real.exp_log ht,← exp_nat_mul]
    apply exp_le_exp.mpr
    have hl := log_le_sub_one_of_pos ht
    nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))]
  have hb := (le_div_iff₀ (exp_pos _)).mpr hb
  apply hb.trans
  calc
    _ ≤ exp ((Fintype.card ι:ℝ)*(Fintype.card κ:ℝ)*h) /
        exp (α*(Fintype.card ι:ℝ)*log h) := div_le_div_of_nonneg_right he (exp_pos _).le
    _ = _ := by rw [← exp_sub]; congr 1; ring

theorem sparse_option_small_entropy {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
      [DecidableEq κ] (s : Finset (ι → Option κ)),
      (∀ f ∈ s, ((optionSupport f).card:ℝ) ≤ α*(Fintype.card ι:ℝ)) →
      (s.card:ℝ) ≤ exp (ε*(Fintype.card ι:ℝ)) := by
  let h : ℝ := min (1/2) (ε/(2*((Fintype.card κ:ℝ)+1)))
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hh1 : h < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hlog : 0 < -log h := neg_pos.mpr (log_neg hh hh1)
  let α := ε/(2*(-log h))
  refine ⟨α,by positivity,?_⟩
  intro ι _ _ _ s hs
  apply (sparse_option_count hh hh1.le s hs).trans
  apply exp_le_exp.mpr
  have hNh : (Fintype.card κ:ℝ)*h ≤ ε/2 := by
    have hd := (le_div_iff₀ (show 0 < 2*((Fintype.card κ:ℝ)+1) by positivity)).mp
      (show h ≤ ε/(2*((Fintype.card κ:ℝ)+1)) from min_le_right _ _)
    nlinarith
  have ha : α*(-log h)=ε/2 := by dsimp [α]; field_simp [ne_of_lt (log_neg hh hh1)]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)

def optionCube (v : ι → ℝ) (grid : κ → ℝ) (f : ι → Option κ) : ι → ℝ :=
  fun i => (f i).elim (v i) grid

omit [Fintype κ] in

theorem sparse_cube_approx [DecidableEq ι] {M ζ α : ℝ} (hζ : 0 < ζ)
    (v a : ι → ℝ) (grid : κ → ℝ) (ha : ∀ i, a i ∈ Icc 0 M)
    (hgrid : ∀ x ∈ Icc (0:ℝ) M, ∃ k, |x-grid k| ≤ ζ)
    (hsq : (∑ i,(a i-v i)^2) ≤ α*ζ^2*(Fintype.card ι:ℝ)) :
    ∃ f : ι → Option κ,
      ((optionSupport f).card:ℝ) ≤ α*(Fintype.card ι:ℝ) ∧
      (∀ i, |a i-optionCube v grid f i| ≤ ζ) ∧
      (∀ i, |optionCube v grid f i-v i| ≤ 2*|a i-v i|) := by
  classical
  choose k hk using (fun i => hgrid (a i) (ha i))
  let f : ι → Option κ := fun i => if ζ < |a i-v i| then some (k i) else none
  have hsupp : optionSupport f = Finset.univ.filter (fun i => ζ < |a i-v i|) := by
    ext i
    simp [optionSupport,f]
  have hb : ((optionSupport f).card:ℝ)*ζ^2 ≤ ∑ i,(a i-v i)^2 := by
    calc
      _ = ∑ i ∈ optionSupport f, ζ^2 := by simp
      _ ≤ ∑ i ∈ optionSupport f, (a i-v i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp (hsupp ▸ hi)).2
        nlinarith [sq_abs (a i-v i)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  refine ⟨f,?_,?_,?_⟩
  · apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hζ)).mp
    calc
      _ ≤ _ := hb.trans hsq
      _ = _ := by ring
  · intro i
    by_cases hi : ζ < |a i-v i|
    · simpa [optionCube,f,hi] using hk i
    · simpa [optionCube,f,hi] using le_of_not_gt hi
  · intro i
    by_cases hi : ζ < |a i-v i|
    · simp only [optionCube,f,hi,ite_eq_left,Option.elim_some]
      have h := abs_sub_le (grid (k i)) (a i) (v i)
      rw [abs_sub_comm (grid (k i)) (a i)] at h
      linarith [hk i]
    · simp [optionCube,f,hi,abs_nonneg]

omit [Fintype ι] [Fintype κ] in
lemma optionCube_bounds {M : ℝ} (v : ι → ℝ) (grid : κ → ℝ)
    (hv : ∀ i, v i ∈ Icc 0 M) (hg : ∀ k,grid k ∈ Icc 0 M) (f : ι → Option κ) :
    ∀ i, optionCube v grid f i ∈ Icc 0 M := by
  intro i
  cases h : f i with
  | none => simpa [optionCube,h] using hv i
  | some k => simpa [optionCube,h] using hg k

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set
open scoped BigOperators

lemma interval_mesh {M ζ : ℝ} (hζ : 0 < ζ) :
    ∃ s : Finset ℝ, (∀ x ∈ s,x ∈ Icc (0:ℝ) M) ∧
      ∀ x ∈ Icc (0:ℝ) M,∃ y ∈ s,|x-y| ≤ ζ := by
  classical
  obtain ⟨s,hs,hfin,hcover⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) M)).finite_cover_balls hζ
  refine ⟨hfin.toFinset,fun x hx => hs (hfin.mem_toFinset.mp hx),?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
  exact ⟨y,hfin.mem_toFinset.mpr hy,(show |x-y| < ζ from Metric.mem_ball.mp hxy).le⟩

theorem sparse_uniform_exponential {M ζ r : ℝ} (hζ : 0 < ζ) (hr : 0 < r) :
    ∃ ε : ℝ,0 < ε ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsFiniteMeasure μ] (n : ℕ) (v : Fin n → ℝ) (_hv : ∀ i,v i ∈ Icc 0 M)
      (E : Set Ω) (GoodHigh GoodLow : (Fin n → ℝ) → Ω → Prop) (C : ℝ),
      0 ≤ C →
      (∀ b, (∀ i,b i ∈ Icc 0 M) → (∑ i,(b i-v i)^2) ≤ 4*ε^2*(n:ℝ) →
        μ.real {ω | ¬GoodHigh b ω} ≤ C*exp (-r*(n:ℝ))) →
      (∀ ω ∈ E,∀ a b, (∀ i,a i ∈ Icc 0 M) → (∀ i,b i ∈ Icc 0 M) →
        (∀ i,|a i-b i| ≤ ζ) → GoodHigh b ω → GoodLow a ω) →
      μ.real {ω | ∃ a, (∀ i,a i ∈ Icc 0 M) ∧ (∑ i,(a i-v i)^2) ≤ ε^2*(n:ℝ) ∧
        ¬GoodLow a ω} ≤ μ.real Eᶜ+C*exp (-(r/2)*(n:ℝ)) := by
  classical
  obtain ⟨grid,hgrid,hcover⟩ := interval_mesh (M := M) hζ
  let κ := {x : ℝ // x ∈ grid}
  obtain ⟨α,hα,hcount⟩ := sparse_option_small_entropy (κ := κ) (half_pos hr)
  let ε := sqrt α*ζ
  have hε : 0 < ε := mul_pos (sqrt_pos.mpr hα) hζ
  have heq : ε^2=α*ζ^2 := by dsimp [ε]; rw [mul_pow,sq_sqrt hα.le]
  refine ⟨ε,hε,?_⟩
  intro Ω _ μ _ n v hv E GoodHigh GoodLow C hC hfixed hnear
  let val : κ → ℝ := Subtype.val
  let s : Finset (Fin n → Option κ) := Finset.univ.filter (fun f =>
    ((optionSupport f).card:ℝ) ≤ α*(n:ℝ) ∧
      (∑ i,(optionCube v val f i-v i)^2) ≤ 4*ε^2*(n:ℝ))
  have hsize : (s.card:ℝ) ≤ exp ((r/2)*(n:ℝ)) := by
    simpa only [Fintype.card_fin] using hcount (Fin n) s (fun f hf => by simpa only [Fintype.card_fin] using (Finset.mem_filter.mp hf).2.1)
  let B : (Fin n → Option κ) → Set Ω := fun f => {ω | ¬GoodHigh (optionCube v val f) ω}
  have hsub : {ω | ∃ a, (∀ i,a i ∈ Icc 0 M) ∧ (∑ i,(a i-v i)^2) ≤ ε^2*(n:ℝ) ∧
        ¬GoodLow a ω} ⊆ Eᶜ ∪ ⋃ f ∈ s,B f := by
    intro ω ⟨a,ha,ha2,hbad⟩
    by_cases hE : ω ∈ E
    · obtain ⟨f,hf,hap,hfp⟩ := sparse_cube_approx hζ v a val ha
        (fun x hx => by obtain ⟨y,hy,hyx⟩ := hcover x hx; exact ⟨⟨y,hy⟩,hyx⟩)
        (by simpa only [Fintype.card_fin,heq] using ha2)
      have hb : ∀ i,optionCube v val f i ∈ Icc 0 M :=
        optionCube_bounds v val hv (fun k => hgrid k.val k.property) f
      have hd : (∑ i,(optionCube v val f i-v i)^2) ≤ 4*ε^2*(n:ℝ) := by
        calc
          _ ≤ ∑ i,4*(a i-v i)^2 := by
            apply Finset.sum_le_sum; intro i _
            have h := hfp i
            have hh := mul_self_le_mul_self (abs_nonneg (optionCube v val f i-v i)) h
            nlinarith only [hh,sq_abs (optionCube v val f i-v i),sq_abs (a i-v i)]
          _ = 4*(∑ i,(a i-v i)^2) := by rw [Finset.mul_sum]
          _ ≤ _ := by linarith
      have hfs : f ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [Fintype.card_fin] using And.intro hf hd⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨f,hfs,fun hg => hbad (hnear ω hE a _ ha hb hap hg)⟩)
    · exact Or.inl hE
  have hsum : (∑ f ∈ s,μ.real (B f)) ≤ (s.card:ℝ)*(C*exp (-r*(n:ℝ))) := by
    calc
      _ ≤ ∑ _f ∈ s,C*exp (-r*(n:ℝ)) := by
        apply Finset.sum_le_sum
        intro f hf
        exact hfixed _ (optionCube_bounds v val hv (fun k => hgrid k.val k.property) f)
          (Finset.mem_filter.mp hf).2.2
      _ = _ := by simp
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measureReal_biUnion_finset_le s B).trans
  apply hsum.trans
  calc
    _ ≤ exp ((r/2)*(n:ℝ))*(C*exp (-r*(n:ℝ))) := mul_le_mul_of_nonneg_right hsize (by positivity)
    _ = _ := by rw [← mul_assoc,mul_comm (exp _) C,mul_assoc,← exp_add]; congr 2; ring
end SKGap
end
end

end OAI
