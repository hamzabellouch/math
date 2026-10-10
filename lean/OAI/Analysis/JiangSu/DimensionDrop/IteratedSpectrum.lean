import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.Separable

namespace OAI

noncomputable section
namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

local instance iteratedStagePNeZero (n : ℕ) : NeZero (stagePair n).p := ⟨(stagePair n).p_pos.ne'⟩
local instance iteratedStageQNeZero (n : ℕ) : NeZero (stagePair n).q := ⟨(stagePair n).q_pos.ne'⟩

abbrev stageMultiplicities (n : ℕ) :=
  canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos

def IteratedIndex (n : ℕ) : ℕ → Type
  | 0 => PUnit
  | k+1 => IteratedIndex n k × SpectralIndex (stageMultiplicities (n+k))

instance iteratedIndexFintype (n k : ℕ) : Fintype (IteratedIndex n k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype (IteratedIndex n k × SpectralIndex (stageMultiplicities (n+k))))

instance iteratedIndexNonempty (n k : ℕ) : Nonempty (IteratedIndex n k) := by
  induction k with
  | zero => exact ⟨PUnit.unit⟩
  | succ k ih =>
    let := ih
    have : Nonempty (SpectralIndex (stageMultiplicities (n+k))) := by
      apply Fintype.card_pos_iff.mp
      rw [spectralIndex_card]
      exact Nat.mul_pos (stageMultiplicities (n+k)).k_pos (stageMultiplicities (n+k)).l_pos
    exact inferInstanceAs (Nonempty (IteratedIndex n k × SpectralIndex (stageMultiplicities (n+k))))

def iteratedFamily (n : ℕ) : (k : ℕ) → IteratedIndex n k → C(Interval,Interval)
  | 0,_ => ContinuousMap.id Interval
  | k+1,i => (iteratedFamily n k i.1).comp (spectralFamily (stageMultiplicities (n+k)) i.2)

lemma spectralTransfer_sum {p q : ℕ} [NeZero p] [NeZero q] (m : Multiplicities p q)
    (z : C(Interval,ℂ)) (t : Interval) :
    spectralTransfer m z t=(Fintype.card (SpectralIndex m):ℂ)⁻¹ *
      ∑ i : SpectralIndex m,z (spectralFamily m i t) := by
  rw [spectralIndex_card]
  simp [spectralTransfer,Fintype.sum_sum_type,spectralFamily,
    ContinuousMap.id_apply,add_assoc]

theorem scalarIterates_sum (n k : ℕ) (z : C(Interval,ℂ)) (t : Interval) :
    scalarIterates n z k t=(Fintype.card (IteratedIndex n k):ℂ)⁻¹ *
      ∑ i : IteratedIndex n k,z (iteratedFamily n k i t) := by
  induction k generalizing t with
  | zero =>
    change z t=(Fintype.card PUnit:ℂ)⁻¹ * ∑ _i : PUnit,z t
    simp
  | succ k ih =>
    rw [scalarIterates,spectralTransfer_sum]
    simp_rw [ih]
    change ((Fintype.card (SpectralIndex (stageMultiplicities (n+k)))):ℂ)⁻¹ *
      (∑ j : SpectralIndex (stageMultiplicities (n+k)),
        (Fintype.card (IteratedIndex n k):ℂ)⁻¹ *
          ∑ i : IteratedIndex n k,z (iteratedFamily n k i (spectralFamily (stageMultiplicities (n+k)) j t))) =
      (Fintype.card (IteratedIndex n k × SpectralIndex (stageMultiplicities (n+k))):ℂ)⁻¹ *
        ∑ i : IteratedIndex n k × SpectralIndex (stageMultiplicities (n+k)),
          z (iteratedFamily n k i.1 (spectralFamily (stageMultiplicities (n+k)) i.2 t))
    rw [Fintype.card_prod,Nat.cast_mul,mul_inv_rev,Fintype.sum_prod_type,
      ←Finset.mul_sum,Finset.sum_comm,mul_assoc]

lemma scalarIterates_sum_re (n k : ℕ) (z : C(Interval,ℂ)) (t : Interval) :
    (scalarIterates n z k t).re=(Fintype.card (IteratedIndex n k):ℝ)⁻¹ *
      ∑ i : IteratedIndex n k,(z (iteratedFamily n k i t)).re := by
  rw [scalarIterates_sum]
  simp [Complex.mul_re,Complex.inv_re,Complex.normSq_natCast]

end JiangSuConstruction

namespace JiangSuCounting
open scoped Topology

abbrev I := Set.Icc (0:ℝ) 1

def falling (a b : ℝ) : C(I,ℝ) :=
  ⟨fun x => max 0 (min 1 ((b-(x:ℝ))/(b-a))),by fun_prop⟩

lemma falling_nonneg (a b : ℝ) (x : I) : 0≤falling a b x := le_max_left _ _
lemma falling_le_one (a b : ℝ) (x : I) : falling a b x≤1 :=
  max_le (by norm_num) (min_le_left _ _)
lemma falling_eq_one {a b : ℝ} (hab : a<b) {x : I} (hx : (x:ℝ)≤a) :
    falling a b x=1 := by
  change max 0 (min 1 ((b-(x:ℝ))/(b-a)))=1
  have hq : 1≤(b-(x:ℝ))/(b-a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  rw [min_eq_left hq,max_eq_right (by norm_num : (0:ℝ)≤1)]
lemma falling_eq_zero {a b : ℝ} (hab : a<b) {x : I} (hx : b≤(x:ℝ)) :
    falling a b x=0 := by
  change max 0 (min 1 ((b-(x:ℝ))/(b-a)))=0
  apply max_eq_left
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

def bump (b c d : ℝ) : C(I,ℝ) :=
  ⟨fun x => (1-falling b c x)*falling c d x,by fun_prop⟩
lemma bump_nonneg (b c d : ℝ) (x : I) : 0≤bump b c d x :=
  mul_nonneg (sub_nonneg.mpr (falling_le_one b c x)) (falling_nonneg c d x)
lemma bump_le_one (b c d : ℝ) (x : I) : bump b c d x≤1 := by
  change (1-falling b c x)*falling c d x≤1
  calc
    (1-falling b c x)*falling c d x ≤ 1*falling c d x :=
      mul_le_mul_of_nonneg_right (sub_le_self _ (falling_nonneg b c x))
        (falling_nonneg c d x)
    _ ≤ 1 := by simpa only [one_mul] using falling_le_one c d x
lemma bump_zero_left {b c d : ℝ} (hbc : b<c) {x : I} (hx : (x:ℝ)≤b) :
    bump b c d x=0 := by simp [bump,falling_eq_one hbc hx]
lemma bump_zero_right {b c d : ℝ} (hcd : c<d) {x : I} (hx : d≤(x:ℝ)) :
    bump b c d x=0 := by simp [bump,falling_eq_zero hcd hx]
lemma bump_one {b c d : ℝ} (hbc : b<c) (hcd : c<d) (hc : c∈Set.Icc (0:ℝ) 1) :
    bump b c d ⟨c,hc⟩=1 := by
  change (1-falling b c ⟨c,hc⟩)*falling c d ⟨c,hc⟩=1
  rw [falling_eq_zero hbc le_rfl,falling_eq_one hcd le_rfl]
  norm_num

lemma falling_add_bump_le_one {a b c d : ℝ} (hab : a<b) (hbc : b<c) (x : I) :
    falling a b x+bump b c d x≤1 := by
  by_cases hx : (x:ℝ)≤b
  · rw [bump_zero_left hbc hx,add_zero]
    exact falling_le_one _ _ _
  · rw [falling_eq_zero hab (le_of_not_ge hx),zero_add]
    exact bump_le_one _ _ _ _

def complexify (f : C(I,ℝ)) : C(I,ℂ) := ⟨fun x => (f x:ℂ),by fun_prop⟩
@[simp] lemma complexify_re (f : C(I,ℝ)) (x : I) : (complexify f x).re=f x := rfl

def cutoff (r δ : ℝ) : C(I,ℂ) := complexify (falling (r+δ/8) (r+δ/4))
def reserve (r δ : ℝ) : C(I,ℂ) :=
  complexify (bump (r+δ/4) (r+3*δ/8) (r+δ/2))

lemma reserve_nonneg (r δ : ℝ) (x : I) : 0≤(reserve r δ x).re := bump_nonneg _ _ _ _
lemma reserve_positive {r δ : ℝ} (hδ : 0<δ) (hr : r∈Set.Icc 0 (1-δ)) :
    ∃ x : I,0<(reserve r δ x).re := by
  have hc : r+3*δ/8∈Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hr.1,hr.2]
  refine ⟨⟨r+3*δ/8,hc⟩,?_⟩
  change 0<bump _ _ _ _
  rw [bump_one (by linarith) (by linarith) hc]
  norm_num

lemma cutoff_source {r δ v : ℝ} (hδ : 0<δ) (hv : |v-r|<δ/8) (x : I) :
    (if (x:ℝ)≤v then (1:ℝ) else 0)≤(cutoff r δ x).re := by
  change _≤falling _ _ x
  split_ifs with hx
  · rw [falling_eq_one (by linarith : r+δ/8<r+δ/4) (by
      have hh := (abs_lt.mp hv).2
      linarith)]
  · exact falling_nonneg _ _ _

lemma cutoff_reserve_target {r δ v : ℝ} (hδ : 0<δ) (hv : |v-r|<δ/8) (x : I) :
    (cutoff r δ x).re+(reserve r δ x).re≤(if (x:ℝ)≤v+δ then (1:ℝ) else 0) := by
  change falling _ _ x+bump _ _ _ x≤_
  split_ifs with hx
  · apply falling_add_bump_le_one <;> linarith
  · have hv' := (abs_lt.mp hv).1
    have hx' : v+δ<(x:ℝ) := lt_of_not_ge hx
    rw [falling_eq_zero (by linarith : r+δ/8<r+δ/4) (by linarith),
      bump_zero_right (by linarith : r+3*δ/8<r+δ/2) (by linarith)]
    norm_num

lemma card_filter_le_of_sums {J : Type*} [Fintype J] [DecidableEq J]
    (x y : J → I) (f g : I → ℝ) (v w : ℝ)
    (hx : ∀ z : I,(if (z:ℝ)≤v then (1:ℝ) else 0)≤f z)
    (hy : ∀ z : I,f z+g z≤(if (z:ℝ)≤w then (1:ℝ) else 0))
    (hm : (∑ j,f (x j))≤(∑ j,f (y j))+(∑ j,g (y j))) :
    (Finset.univ.filter fun j => (x j:ℝ)≤v).card≤
      (Finset.univ.filter fun j => (y j:ℝ)≤w).card := by
  have h₁ := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hx (x j))
  have h₂ := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hy (y j))
  rw [Finset.sum_add_distrib] at h₂
  have hh := h₁.trans (hm.trans h₂)
  exact_mod_cast (show ((Finset.univ.filter fun j => (x j:ℝ)≤v).card:ℝ) ≤
    (Finset.univ.filter fun j => (y j:ℝ)≤w).card from by simpa only [Finset.sum_boole] using hh)

end JiangSuCounting

namespace JiangSuConstruction
open Filter JiangSuCounting
open scoped Topology

lemma cumulative_counts_near (n : ℕ) {r δ : ℝ} (hδ : 0<δ)
    (hr : r∈Set.Icc 0 (1-δ)) :
    ∃ k : ℕ,∀ l, k≤l → ∀ s t : Interval,∀ v : ℝ, |v-r|<δ/8 →
      (Finset.univ.filter fun i : IteratedIndex n l => (iteratedFamily n l i s:ℝ)≤v).card≤
      (Finset.univ.filter fun i : IteratedIndex n l => (iteratedFamily n l i t:ℝ)≤v+δ).card := by
  classical
  let f := cutoff r δ
  let g := reserve r δ
  obtain ⟨x,hx⟩ := reserve_positive hδ hr
  obtain ⟨b,kb,hb,hkb⟩ := scalarIterates_eventually_positive n g (reserve_nonneg r δ) x hx
  obtain ⟨kf,hkf⟩ := scalarIterates_eventually_oscillation n f hb
  refine ⟨max kb kf,?_⟩
  intro l hl s t v hv
  have hlow := hkb l ((le_max_left kb kf).trans hl) t
  have hosc := hkf l ((le_max_right kb kf).trans hl) s t
  have hre := Complex.re_le_norm (scalarIterates n f l s-scalarIterates n f l t)
  rw [Complex.sub_re] at hre
  have hmean : (scalarIterates n f l s).re≤
      (scalarIterates n f l t).re+(scalarIterates n g l t).re := by linarith
  simp only [scalarIterates_sum_re] at hmean
  rw [←mul_add] at hmean
  have hI : (0:ℝ)<(Fintype.card (IteratedIndex n l):ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsum := le_of_mul_le_mul_left hmean (inv_pos.mpr hI)
  exact card_filter_le_of_sums (fun i => iteratedFamily n l i s)
    (fun i => iteratedFamily n l i t) (fun z => (f z).re) (fun z => (g z).re) v (v+δ)
    (cutoff_source hδ hv) (cutoff_reserve_target hδ hv) hsum

theorem iterated_spectrum_shifted_counts (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ k : ℕ,∀ l, k≤l → ∀ s t : Interval,∀ v : ℝ,
      (Finset.univ.filter fun i : IteratedIndex n l => (iteratedFamily n l i s:ℝ)≤v).card≤
      (Finset.univ.filter fun i : IteratedIndex n l => (iteratedFamily n l i t:ℝ)≤v+δ).card := by
  classical
  obtain ⟨T,hTK,hT,hcover⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) (1-δ))).finite_cover_balls
    (show 0<δ/8 by positivity : 0<δ/8)
  let R : Finset ℝ := hT.toFinset
  have he (r : ℝ) (hr : r∈R) : ∀ᶠ l : ℕ in atTop,
      ∀ s t : Interval,∀ v : ℝ, |v-r|<δ/8 →
        (Finset.univ.filter fun i : IteratedIndex n l => (iteratedFamily n l i s:ℝ)≤v).card≤
        (Finset.univ.filter fun i : IteratedIndex n l => (iteratedFamily n l i t:ℝ)≤v+δ).card := by
    have hrT : r∈T := (hT.mem_toFinset).mp hr
    obtain ⟨k,hk⟩ := cumulative_counts_near n hδ (hTK hrT)
    exact eventually_atTop.mpr ⟨k,hk⟩
  obtain ⟨k,hk⟩ := eventually_atTop.mp ((eventually_all_finset R).mpr he)
  refine ⟨k,?_⟩
  intro l hl s t v
  by_cases hv : v<0
  · have hzero : (Finset.univ.filter fun i : IteratedIndex n l =>
        (iteratedFamily n l i s:ℝ)≤v)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      linarith [(iteratedFamily n l i s).property.1]
    rw [hzero,Finset.card_empty]
    exact Nat.zero_le _
  · by_cases hw : 1≤v+δ
    · have hall : (Finset.univ.filter fun i : IteratedIndex n l =>
          (iteratedFamily n l i t:ℝ)≤v+δ)=Finset.univ := by
        apply Finset.filter_eq_self.mpr
        intro i hi
        exact (iteratedFamily n l i t).property.2.trans hw
      rw [hall]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    · have hvK : v∈Set.Icc 0 (1-δ) := ⟨le_of_not_gt hv,by linarith⟩
      obtain ⟨r,hrT,hvr⟩ := Set.mem_iUnion₂.mp (hcover hvK)
      have hrR : r∈R := hT.mem_toFinset.mpr hrT
      have hdist : |v-r|<δ/8 := hvr
      exact hk l hl r hrR s t v hdist

end JiangSuConstruction

end

end OAI
