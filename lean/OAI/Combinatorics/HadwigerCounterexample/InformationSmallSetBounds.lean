import OAI.Combinatorics.HadwigerCounterexample.UnfilteredHistogramEnergy

namespace OAI

/-! # Information Small Set Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real
open scoped BigOperators
variable {A B C X : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X]

/-- Family of orientation/flag-conditional laws (μ already
realizes joint flag law). -/
structure Ultra (μ : Wgt A) (p : A→Wgt B) : Prop where
  law : IsLaw μ
  labs : ∀ i,IsLaw (p i)

variable {μ : Wgt A} {p : A→Wgt B}

def budget (μ : Wgt A) (p : A→Wgt B) (f : B→ C) :=
  avg μ (fun i => tension (mapW (p i) f) (mapW unif f))
def tariffs (μ : Wgt A) (p : A→ Wgt B) (r : ℕ) (δ V : ℝ) :=
  ∀ (C : Type) [Fintype C],Fintype.card C≤ r →
    ∀ (f : B→ C), stamina (mapW unif f) δ → budget μ p f ≤ V

def catalog (μ : Wgt A) (p : A→Wgt B) (w : Wgt B) :=
  ∃ t : Wgt A,(∀ i,0 ≤ t i) ∧ (∀ i,t i≤ μ i) ∧ w=mixW t p
namespace Ultra

variable [Nonempty B] (h : Ultra μ p)

omit [Nonempty B] in
theorem maxCat (h : Ultra μ p) : IsLaw (mixW μ p) := mixW_law h.law h.labs
omit [Nonempty B] in
theorem cat_dom (h : Ultra μ p) (w : Wgt B) (hw : catalog μ p w) :
    (∀ i, 0 ≤ w i) ∧ (∀ i, w i ≤ mixW μ p i) := by
  obtain ⟨t,hp,hq,rfl⟩ := hw
  exact ⟨fun i => avg_nonneg hp (fun j => (h.labs j).nz _),fun i => avg_mono_left
    (fun j => (h.labs j).nz _) hq⟩

omit [Nonempty B] in
theorem cat_sub (h : Ultra μ p) (w : Wgt B) (hw : catalog μ p w) :
    SubLaw w := by
  obtain ⟨h1,h2⟩ := h.cat_dom w hw
  exact ⟨h1,(Finset.sum_le_sum fun i _ => h2 i).trans_eq h.maxCat.total⟩

end Ultra

private theorem binary_info (q w : Wgt Bool) (hq : IsLaw q) (hw : IsLaw w)
    (L : ℝ) (he : 0 < q true) (h : q true ≤ exp (-L)) :
    w true * L-log 2 ≤ tension w q := by
  have h1 := Real.log_le_log he h
  rw [Real.log_exp] at h1
  have h2 : log (q false)≤0 := log_nonpos (hq.nz _) (hq.weight_le_one _)
  rw [tension_as_diff]
  have hh : -log 2 ≤ negEnt w := by simpa using log_card_le_negEnt hw
  simp only [avg,Fintype.sum_bool]
  linarith only [hh,mul_nonpos_of_nonneg_of_nonpos (hw.nz false) h2,
    mul_le_mul_of_nonneg_left h1 (hw.nz true)]

theorem expand_event {w : Wgt B} (hw : IsLaw w) (P : B→Prop) (δ : ℝ)
    (he : 2*δ < 1) (hm : ∀ x,w x ≤ δ) (hP : pr w P ≤ 2*δ) :
    ∃ Q : B→Prop,(∀ x,P x → Q x) ∧ δ ≤ pr w Q ∧ pr w Q ≤2*δ := by
  classical
  let S := Finset.univ.filter P
  let M := Finset.univ.filter (fun T : Finset B => S ⊆ T ∧ pr w (·∈T) ≤2*δ)
  have hS (i : B) : i∈S ↔ P i := by simp [S]
  have hh : S∈M := mem_filter.mpr ⟨mem_univ _,(by simp_rw [hS]; exact ⟨le_rfl,hP⟩)⟩
  obtain ⟨T,hT,hmax⟩ := Finset.exists_max_image M Finset.card ⟨S,hh⟩
  obtain ⟨hx,hz⟩ := (mem_filter.mp hT).2
  refine ⟨(·∈T),fun i hi => hx ((hS i).mpr hi),?_,hz⟩
  by_contra! h
  obtain ⟨i,hi⟩ : ∃ i,i∉T := by
    by_contra! hs
    simp only [hs,pr_true,hw.total] at hz
    linarith
  let T' := insert i T
  have hh' : pr w (·∈T') ≤ w i + pr w (·∈T) :=
    le_trans (le_of_eq (congrArg (pr w) (funext fun i => propext (Finset.mem_insert))))
      ((pr_or_le hw.nz).trans_eq (by simp))
  have ht : T' ∈ M := mem_filter.mpr
    ⟨mem_univ _,hx.trans (subset_insert ..),by linarith only [hh',h,hm i]⟩
  specialize hmax _ ht
  rw [show T'.card=T.card+1 from Finset.card_insert_of_notMem hi] at hmax
  omega

set_option maxHeartbeats 800000 in
theorem ui_threshold (V η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ δ≤1 ∧
    ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty B]
      (μ : Wgt A) (p : A→ Wgt B), Ultra μ p →
      tariffs μ p 2 δ V →
      ∀ S : B→Prop, pr unif S ≤δ → pr (mixW μ p) S ≤ η := by
  classical
  obtain ⟨L,hL,hL'⟩ : ∃ L : ℝ,0<L ∧ V+log 2≤ η*L := by
    obtain ⟨L,hL⟩ := exists_gt (max 0 ((V+log 2)/η))
    exact ⟨L,lt_of_le_of_lt (le_max_left ..) hL,
      by rw [mul_comm]; exact (div_le_iff₀ hη).mp ((le_max_right ..).trans hL.le)⟩
  let δ := min (exp (-L)/2) (1/4)
  have h0 := min_le_left (exp (-L)/2) (1/4)
  change δ≤ _ at h0
  have h1 := min_le_right (exp (-L)/2) (1/4)
  change δ ≤ _ at h1
  have hδ : 0<δ := by unfold δ; exact lt_min (by positivity) (by norm_num)
  refine ⟨δ,hδ,by linarith,fun A B _ _ _ μ p hw ht S hS => ?_⟩
  have he : IsLaw (unif : Wgt B) := unif_law
  by_cases hy : ∃ i,S i
  · obtain ⟨i,hi⟩ := hy
    have hh (j : B) : unif j ≤δ := by
      rw [show unif j=unif i from by simp [unif_apply],← pr_point' unif i]
      exact (pr_mono he.nz (fun j (h:j=i) => h.symm ▸ hi)).trans hS
    obtain ⟨Q,hq,hQ,hQ'⟩ := expand_event he S δ (by linarith) hh (by linarith)
    let f := fun x : B => decide (Q x)
    let q := mapW (unif : Wgt B) f
    have hqL := mapW_law he f
    have hf (w : Wgt B) : mapW w f true=pr w Q := by simp [mapW,f]
    have hq1 : δ≤q true := by unfold q; rw [hf]; exact hQ
    have hq2 : q true ≤2*δ := by unfold q; rw [hf]; exact hQ'
    have hE : budget μ p f ≤ V := ht Bool (by simp) f (by
      rintro (a|a) _
      case false =>
        have hh : q true+q false=1 := by
          have h := hqL.total; rw [tot,Fintype.sum_bool] at h; exact h
        change δ≤q false; linarith only [hh,hq2,h1]
      case true => exact hq1)
    have hi (j : A) :
        pr (p j) Q*L-log 2 ≤ tension (mapW (p j) f) q := by
      rw [← hf]; exact binary_info q _ hqL (mapW_law (hw.labs j) _) L (hδ.trans_le hq1)
        (by linarith only [hq2,h0])
    have hz := avg_mono hw.law.nz hi
    rw [avg_sub,avg_mul,hw.law.avg_const] at hz
    change avg μ (fun i => pr (p i) Q) * _-_ ≤ budget μ p f at hz
    have hv : pr (mixW μ p) Q=avg μ (fun i => pr (p i) Q) := mixW_avg ..
    apply (pr_mono hw.maxCat.nz hq).trans
    rw [hv]
    exact le_of_mul_le_mul_right (by linarith only [hz,hE,hL']) hL
  have ht (i) : ¬ S i := fun h => hy ⟨i,h⟩
  simp [pr,ht,hη.le]
end HadwigerCounterexample

end

end OAI
