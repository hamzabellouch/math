import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerBasic
import OAI.Analysis.JiangSu.MatrixAlgebras.ProjectionGapIsometry

namespace OAI

noncomputable section
namespace DirectComparison
open Pureness Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma isometry_diagonal_choice (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ)≤atTop) (P : ℕ → ℕ → Prop)
    (hP : ∀ m, ∀ᶠ k in (U : Filter ℕ), P m k) :
    ∃ j : ℕ → ℕ, Tendsto j (U : Filter ℕ) atTop ∧
      ∀ᶠ k in (U : Filter ℕ), P (j k) k := by
  classical
  let j : ℕ → ℕ := fun k => Nat.findGreatest (fun n => ∀ m≤n,P m k) k
  have hfin (n : ℕ) : ∀ᶠ k in (U : Filter ℕ), ∀ m≤n,P m k := by
    have h := (eventually_all_finset (Finset.range (n+1))).mpr (fun m _ => hP m)
    filter_upwards [h] with k hk
    intro m hm
    exact hk m (Finset.mem_range.mpr (by omega))
  refine ⟨j,?_,?_⟩
  · apply tendsto_atTop.mpr
    intro n
    filter_upwards [hfin n,hfree (eventually_ge_atTop n)] with k hk hnk
    exact Nat.le_findGreatest hnk hk
  · filter_upwards [hfin 0] with k hk
    exact (Nat.findGreatest_spec (P := fun n => ∀ m≤n,P m k) (Nat.zero_le k) hk) (j k) le_rfl

theorem small_trace_norm_ultrapower [Nonempty (TracialState A)]
    (hcmp : StrictComparison A) (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ)≤atTop)
    (e f : lp (fun _ : ℕ => A) ∞)
    (he : ∀ n,0≤e n) (hen : ∀ n,‖e n‖≤1)
    (hf : ∀ n,0≤f n) (hfn : ∀ n,‖f n‖≤1)
    (c : ℝ) (hc : 0<c)
    (hsmall : ∀ r : ℝ,0<r → ∀ᶠ n in (U : Filter ℕ),
      ∀ τ : TracialState A,(τ.functional (e n)).re<r)
    (hlarge : ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,c≤(τ.functional (f n)).re)
    (hdefect : ∀ r : ℝ,0<r → ∀ᶠ n in (U : Filter ℕ),
      ∀ τ : TracialState A,(τ.functional (f n-f n*f n)).re<r) :
    ∃ s : NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      star s*s=NormUltra.QuotientAlgebra.mk U e ∧
      NormUltra.QuotientAlgebra.mk U f*s=s := by
  classical
  let d : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hd (n : ℕ) : 0<d n := by dsimp [d]; positivity
  have hd1 (n : ℕ) : d n≤1 := by
    dsimp [d]
    exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hd0 : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P : ℕ → ℕ → Prop := fun m n =>
    (∀ τ : TracialState A,(τ.functional (e n)).re<d m*c/2) ∧
    (∀ τ : TracialState A,c≤(τ.functional (f n)).re) ∧
    (∀ τ : TracialState A,(τ.functional (f n-f n*f n)).re<d m*c/2)
  have hP (m : ℕ) : ∀ᶠ n in (U : Filter ℕ),P m n := by
    exact (hsmall _ (by positivity)).and (hlarge.and (hdefect _ (by positivity)))
  obtain ⟨j,hj,hjP⟩ := isometry_diagonal_choice U hfree P hP
  have hlocal (n : ℕ) (hn : P (j n) n) :
      ∃ s : A,‖s‖≤2 ∧ ‖star s*s-e n‖<2*d (j n) ∧ ‖f n*s-s‖≤2*d (j n) := by
    obtain ⟨s,hs,hse,hsf⟩ := small_trace_peak_isometry hcmp (e n) (f n)
      (he n) (hen n) (hf n) (hfn n) (d (j n)) (d (j n)) c (d (j n))
      (hd _) (hd _) hc (hd _) (hd1 _) hn.1 hn.2.1 hn.2.2
    exact ⟨s,hs,by linarith,hsf⟩
  let s : ℕ → A := fun n => if hn : P (j n) n then (hlocal n hn).choose else 0
  have hsn (n : ℕ) : ‖s n‖≤2 := by
    dsimp [s]
    split_ifs with hn
    · exact (hlocal n hn).choose_spec.1
    · simp
  let b : lp (fun _ : ℕ => A) ∞ := ⟨s,memℓp_infty ⟨2,by
    rintro _ ⟨n,rfl⟩
    exact hsn n⟩⟩
  have hse : Tendsto (fun n => ‖star (b n)*b n-e n‖) (U : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_
      (by simpa using (tendsto_const_nhds (x := (2:ℝ))).mul (hd0.comp hj))
    filter_upwards [hjP] with n hn
    change ‖star (s n)*s n-e n‖≤2*d (j n)
    simp only [s,dite_eq_left hn]
    exact (hlocal n hn).choose_spec.2.1.le
  have hsf : Tendsto (fun n => ‖f n*b n-b n‖) (U : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_
      (by simpa using (tendsto_const_nhds (x := (2:ℝ))).mul (hd0.comp hj))
    filter_upwards [hjP] with n hn
    change ‖f n*s n-s n‖≤2*d (j n)
    simp only [s,dite_eq_left hn]
    exact (hlocal n hn).choose_spec.2.2
  refine ⟨NormUltra.QuotientAlgebra.mk U b,?_,?_⟩
  · rw [←NormUltra.QuotientAlgebra.mk_star,←NormUltra.QuotientAlgebra.mk_mul,
      NormUltra.QuotientAlgebra.mk_eq_mk_iff]
    exact hse
  · rw [←NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_eq_mk_iff]
    exact hsf

theorem projection_gap_norm_ultrapower [Nonempty (TracialState A)]
    (hcmp : StrictComparison A) (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ)≤atTop)
    (e f : lp (fun _ : ℕ => A) ∞)
    (he : ∀ n,0≤e n) (hen : ∀ n,‖e n‖≤1)
    (hf : ∀ n,0≤f n) (hfn : ∀ n,‖f n‖≤1)
    (c : ℝ) (hc : 0<c)
    (hede : ∀ r : ℝ,0<r → ∀ᶠ n in (U : Filter ℕ),
      ∀ τ : TracialState A,(τ.functional (e n-e n*e n)).re<r)
    (hgap : ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
      (τ.functional (e n)).re+c≤(τ.functional (f n)).re)
    (hfde : ∀ r : ℝ,0<r → ∀ᶠ n in (U : Filter ℕ),
      ∀ τ : TracialState A,(τ.functional (f n-f n*f n)).re<r) :
    ∃ s : NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      star s*s=NormUltra.QuotientAlgebra.mk U e ∧
      NormUltra.QuotientAlgebra.mk U f*s=s := by
  classical
  let d : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hd (n : ℕ) : 0<d n := by dsimp [d]; positivity
  have hd1 (n : ℕ) : d n≤1 := by
    dsimp [d]
    exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hd0 : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P : ℕ → ℕ → Prop := fun m n =>
    (∀ τ : TracialState A,(τ.functional (e n-e n*e n)).re<d m*c/3) ∧
    (∀ τ : TracialState A,(τ.functional (e n)).re+c≤(τ.functional (f n)).re) ∧
    (∀ τ : TracialState A,(τ.functional (f n-f n*f n)).re<d m*c/3)
  have hP (m : ℕ) : ∀ᶠ n in (U : Filter ℕ),P m n := by
    exact (hede _ (by positivity)).and (hgap.and (hfde _ (by positivity)))
  obtain ⟨j,hj,hjP⟩ := isometry_diagonal_choice U hfree P hP
  have hlocal (n : ℕ) (hn : P (j n) n) :
      ∃ s : A,‖s‖≤2 ∧ ‖star s*s-e n‖<2*d (j n) ∧ ‖f n*s-s‖≤2*d (j n) := by
    obtain ⟨s,hs,hse,hsf⟩ := projection_gap_isometry hcmp (e n) (f n)
      (he n) (hen n) (hf n) (hfn n) (d (j n)) (d (j n)) c (d (j n))
      (hd _) (hd _) hc (hd _) (hd1 _) hn.2.1 hn.1 hn.2.2
    exact ⟨s,hs,by linarith,hsf⟩
  let s : ℕ → A := fun n => if hn : P (j n) n then (hlocal n hn).choose else 0
  have hsn (n : ℕ) : ‖s n‖≤2 := by
    dsimp [s]
    split_ifs with hn
    · exact (hlocal n hn).choose_spec.1
    · simp
  let b : lp (fun _ : ℕ => A) ∞ := ⟨s,memℓp_infty ⟨2,by
    rintro _ ⟨n,rfl⟩
    exact hsn n⟩⟩
  have hse : Tendsto (fun n => ‖star (b n)*b n-e n‖) (U : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_
      (by simpa using (tendsto_const_nhds (x := (2:ℝ))).mul (hd0.comp hj))
    filter_upwards [hjP] with n hn
    change ‖star (s n)*s n-e n‖≤2*d (j n)
    simp only [s,dite_eq_left hn]
    exact (hlocal n hn).choose_spec.2.1.le
  have hsf : Tendsto (fun n => ‖f n*b n-b n‖) (U : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_
      (by simpa using (tendsto_const_nhds (x := (2:ℝ))).mul (hd0.comp hj))
    filter_upwards [hjP] with n hn
    change ‖f n*s n-s n‖≤2*d (j n)
    simp only [s,dite_eq_left hn]
    exact (hlocal n hn).choose_spec.2.2
  refine ⟨NormUltra.QuotientAlgebra.mk U b,?_,?_⟩
  · rw [←NormUltra.QuotientAlgebra.mk_star,←NormUltra.QuotientAlgebra.mk_mul,
      NormUltra.QuotientAlgebra.mk_eq_mk_iff]
    exact hse
  · rw [←NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_eq_mk_iff]
    exact hsf

end DirectComparison

end

end OAI
