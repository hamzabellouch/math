import OAI.Analysis.LipschitzHilbert.Fourier.AnnularL2Resolution
import OAI.Analysis.LipschitzHilbert.Packets.VerticalFrameBound
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteEnergySchur

namespace OAI

/-! The concrete annular resolution also supplies the lower square-frame
bound: at each frequency only three of its summands can be nonzero. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem natural_annular_nonzero_count (I : Finset ℕ) (x : ℝ) :
    (I.filter (fun n => reassemblyDifference ((3/2:ℝ)^n*x)≠0)).card≤3 := by
  classical
  let A := I.filter (fun n => reassemblyDifference ((3/2:ℝ)^n*x)≠0)
  change A.card≤3
  have hsep (j k : ℕ) (hjk : j+2≤k) :
      reassemblyDifference ((3/2:ℝ)^j*x)=0 ∨ reassemblyDifference ((3/2:ℝ)^k*x)=0 := by
    simpa only [zpow_natCast] using geometric_annuli_separated (j:ℤ) (k:ℤ) x (by exact_mod_cast hjk)
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hjnz := (Finset.mem_filter.mp hj).2
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      have hknz := (Finset.mem_filter.mp hk).2
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        have hkj : k+2≤j := by omega
        exact (hsep k j hkj).elim hknz hjnz
      · by_contra hn
        have hjk : j+2≤k := by omega
        exact (hsep j k hjk).elim hjnz hknz
    apply (Finset.card_le_card hsub).trans
    rw [Nat.card_Icc]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega


theorem natural_annular_square_sum (I : Finset ℕ) (x : ℝ) :
    (∑ n∈I, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2)≤12 := by
  classical
  let A := I.filter (fun n => reassemblyDifference ((3/2:ℝ)^n*x)≠0)
  have heq : (∑ n∈I, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2)=
      ∑ n∈A, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : reassemblyDifference ((3/2:ℝ)^n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  rw [heq]
  calc
    _ ≤ ∑ n∈A, (4:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [show (2:ℝ)^2=4 by norm_num] using
        pow_le_pow_left₀ (norm_nonneg _) (reassemblyDifference_norm ((3/2:ℝ)^n*x)) 2
    _ = (A.card:ℝ)*4 := by simp
    _ ≤ 12 := by
      have hc : (A.card:ℝ)≤3 := by exact_mod_cast natural_annular_nonzero_count I x
      linarith

theorem reassemblyScale_square_sum (N : ℕ) (x : ℝ) :
    (∑ n∈Finset.range (2*N+1), ‖reassemblyDifference (reassemblyScale N n*x)‖^2)≤12 := by
  have he (n : ℕ) : reassemblyScale N n*x=(3/2:ℝ)^n*((2/3:ℝ)^N*x) := by
    unfold reassemblyScale
    ring
  simpa only [he] using natural_annular_square_sum (Finset.range (2*N+1)) ((2/3:ℝ)^N*x)

theorem annular_upper_frame (N : ℕ) (f : Lp ℂ 2 planeMeasure) :
    (∑ n∈Finset.range (2*N+1),
      ‖verticalL2Projection reassemblyDifferenceSchwartz (reassemblyScale N n) f‖^2)≤12*‖f‖^2 := by
  apply verticalFrame_L2 _ _ _ (reassemblyScale_pos N) 12
  intro eta
  simpa only [reassemblyDifferenceSchwartz_apply] using reassemblyScale_square_sum N eta

theorem natural_annular_sum_square (I : Finset ℕ) (x : ℝ) :
    ‖∑ n∈I, reassemblyDifference ((3/2:ℝ)^n*x)‖^2≤
      3*∑ n∈I, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2 := by
  classical
  let A := I.filter (fun n => reassemblyDifference ((3/2:ℝ)^n*x)≠0)
  have heq : (∑ n∈I, reassemblyDifference ((3/2:ℝ)^n*x))=
      ∑ n∈A, reassemblyDifference ((3/2:ℝ)^n*x) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    by_contra h
    exact hnA (Finset.mem_filter.mpr ⟨hn,h⟩)
  have hs : (∑ n∈A, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2)=
      ∑ n∈I, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : reassemblyDifference ((3/2:ℝ)^n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  have hc : (A.card:ℝ)≤3 := by exact_mod_cast natural_annular_nonzero_count I x
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A
    (f:=fun _ => (1:ℝ)) (g:=fun n => ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2)
    (r:=fun n => ‖reassemblyDifference ((3/2:ℝ)^n*x)‖)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  rw [heq]
  calc
    _ ≤ (∑ n∈A, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (A.card:ℝ)*(∑ n∈A, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2) := hcs
    _ ≤ 3*(∑ n∈A, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2) :=
      mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [hs]

theorem reassemblySymbol_square_le (N : ℕ) (x : ℝ) :
    ‖reassemblySymbol N x‖^2≤
      3*∑ n∈Finset.range (2*N+1), ‖reassemblyDifference (reassemblyScale N n*x)‖^2 := by
  have he (n : ℕ) : reassemblyScale N n*x=(3/2:ℝ)^n*((2/3:ℝ)^N*x) := by
    unfold reassemblyScale
    ring
  simpa only [reassemblySymbol,he] using natural_annular_sum_square (Finset.range (2*N+1)) ((2/3:ℝ)^N*x)

theorem annularL2Sum_lower_frame_schwartz (N : ℕ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖annularL2Sum N (f.toLp 2 planeMeasure)‖^2≤
      3*∑ n∈Finset.range (2*N+1),
        ‖verticalL2Projection reassemblyDifferenceSchwartz (reassemblyScale N n)
          (f.toLp 2 planeMeasure)‖^2 := by
  have hi (n : ℕ) : Integrable (fun omega =>
      ‖planarFourier (schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f) omega‖^2)
      planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz (schwartzVerticalProjection reassemblyDifferenceSchwartz
        (reassemblyScale N n) 0 f)).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  have hsum : Integrable (fun omega => ‖planarFourier (schwartzAnnularSum N f) omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz (schwartzAnnularSum N f)).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  have h := integral_mono hsum ((integrable_finsetSum _ (fun n _ => hi n)).const_mul 3) (fun omega => by
    rw [schwartzAnnularSum_fourier,norm_mul,mul_pow]
    simp only [schwartzVerticalProjection_fourier,sub_zero,reassemblyDifferenceSchwartz_apply,norm_mul,mul_pow]
    rw [←Finset.sum_mul]
    nlinarith only [mul_le_mul_of_nonneg_right (reassemblySymbol_square_le N omega.2)
      (sq_nonneg ‖planarFourier f omega‖)])
  rw [integral_const_mul,integral_finsetSum _ (fun n _ => hi n)] at h
  simp_rw [planar_integral_norm_sq_fourier] at h
  have hlo := memLp_toL2_norm_sq planeMeasure (schwartzAnnularSum N f) ((schwartzAnnularSum N f).memLp 2 planeMeasure)
  change ‖(schwartzAnnularSum N f).toLp 2 planeMeasure‖^2=_ at hlo
  rw [annularL2Sum_onSchwartz,hlo]
  have heq (n : ℕ) :
      ‖verticalL2Projection reassemblyDifferenceSchwartz (reassemblyScale N n) (f.toLp 2 planeMeasure)‖^2=
        ∫ z, ‖schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f z‖^2 ∂planeMeasure := by
    rw [verticalL2Projection_onSchwartz _ _ (reassemblyScale_pos _ _)]
    exact memLp_toL2_norm_sq planeMeasure _ ((schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f).memLp 2 planeMeasure)
  simpa only [heq] using h

theorem annularL2Sum_lower_frame (N : ℕ) (f : Lp ℂ 2 planeMeasure) :
    ‖annularL2Sum N f‖^2≤3*∑ n∈Finset.range (2*N+1),
      ‖verticalL2Projection reassemblyDifferenceSchwartz (reassemblyScale N n) f‖^2 := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  exact hd.induction_on f (isClosed_le (by fun_prop) (by fun_prop)) (annularL2Sum_lower_frame_schwartz N)

end LipschitzHilbert.PacketRepresentation

end

end OAI
