import OAI.Analysis.AncientFlat.Evolution.InitialCore
import OAI.Analysis.AncientFlat.Geometry.WindowHolderCover

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicInitial
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def openSlab (R h : ℝ) : Set (V × ℝ) := {p | ‖p.1‖<R ∧ p.2∈Ico 0 h}
omit [FiniteDimensional ℝ V] in
lemma initial_close_pair_window {r h q : ℝ} (hq : 0<q) (p z : V × ℝ)
    (hp : p∈openSlab r h) (hz : z∈openSlab r h) (hd : pdist p z<q) :
    let p0 : V × ℝ := (p.1,max p.2 z.2)
    p0∈openSlab r h ∧ windowInv p0 q p∈cylinder 1 ∧ windowInv p0 q z∈cylinder 1 := by
  dsimp only
  have ht : |p.2-z.2|<q^4 := by
    have hh : |p.2-z.2|^((1:ℝ)/4)<q := by
      dsimp [pdist] at hd; linarith [norm_nonneg (p.1-z.1)]
    have hh' : (|p.2-z.2|^((1:ℝ)/4))^4<q^4 := by gcongr
    rwa [pow_quarter_four (abs_nonneg _)] at hh'
  have hx : ‖p.1-z.1‖<q := by
    dsimp [pdist] at hd; linarith [Real.rpow_nonneg (abs_nonneg (p.2-z.2)) ((1:ℝ)/4)]
  have ht1 : |p.2-max p.2 z.2|<q^4 := by
    rcases le_total p.2 z.2 with h | h
    · simpa only [max_eq_right h] using ht
    · simp only [max_eq_left h,sub_self,abs_zero]; positivity
  have ht2 : |z.2-max p.2 z.2|<q^4 := by
    rcases le_total p.2 z.2 with h | h
    · simp only [max_eq_right h,sub_self,abs_zero]; positivity
    · simpa only [max_eq_left h,abs_sub_comm] using ht
  refine ⟨⟨hp.1,hp.2.1.trans (le_max_left _ _),max_lt hp.2.2 hz.2.2⟩,?_,?_⟩
  · exact windowInv_mem_one _ hq p (by simpa using hq) ht1 (le_max_left _ _)
  · exact windowInv_mem_one _ hq z (by simpa only [norm_sub_rev] using hx) ht2 (le_max_right _ _)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [FiniteDimensional ℝ V] in
lemma holder_of_initial_windows {α q C r H : ℝ} (hα : 0≤α) (hq : 0<q) (hq1 : q≤1) (hC : 0≤C)
    (n : ℕ) (hn : n≤4) (f : V × ℝ → E)
    (h : ∀ p0∈openSlab r H, HolderBound α (cylinder 1) (fun p => q^n • f (window p0 q p)) C) :
    HolderBound α (openSlab r H) f (2*C/(q^4*q^α)) := by
  let B := C/(q^4*q^α)
  have hqa : 0<q^α := Real.rpow_pos_of_pos hq _
  have hB : 0≤B := by dsimp [B]; positivity
  have hq4 : q^4≤q^n := pow_le_pow_of_le_one hq.le hq1 hn
  have hqa1 : q^α≤1 := Real.rpow_le_one hq.le hq1 hα
  have heq : q^4*q^α*B=C := by dsimp [B]; field_simp
  have hCB : C≤q^n*q^α*B := by rw [←heq]; gcongr
  have Hw (p0 : V × ℝ) (hp0 : p0∈openSlab r H) :=
    unscale_holder hq p0 (cylinder 1) n f ((h p0 hp0).mono hCB)
  have Hsup (p : V × ℝ) (hp : p∈openSlab r H) : ‖f p‖≤B*q^α := by
    have hz : ((0:V),(0:ℝ))∈cylinder 1 := by norm_num [cylinder]
    simpa only [window_zero] using (Hw p hp).1 (0,0) hz
  have HB : 2*B=2*C/(q^4*q^α) := by dsimp [B]; ring
  rw [←HB]
  constructor
  · intro p hp
    exact (Hsup p hp).trans (by nlinarith)
  · intro p hp z hz
    by_cases hnear : pdist p z<q
    · obtain ⟨hctr,hip,hiz⟩ := initial_close_pair_window hq p z hp hz hnear
      have hc := (Hw (p.1,max p.2 z.2) hctr).2 (windowInv (p.1,max p.2 z.2) q p) hip
        (windowInv (p.1,max p.2 z.2) q z) hiz
      simp only [window_windowInv _ hq.ne'] at hc
      exact hc.trans (mul_le_mul_of_nonneg_right (by linarith : B≤2*B) (Real.rpow_nonneg (pdist_nonneg p z) _))
    · have hdq : q≤pdist p z := le_of_not_gt hnear
      calc
        _≤‖f p‖+‖f z‖ := norm_sub_le _ _
        _≤B*q^α+B*q^α := add_le_add (Hsup p hp) (Hsup z hz)
        _=(2*B)*q^α := by ring
        _≤(2*B)*pdist p z^α := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq.le hdq hα) (by positivity)
end ParabolicInitial

end

end OAI
