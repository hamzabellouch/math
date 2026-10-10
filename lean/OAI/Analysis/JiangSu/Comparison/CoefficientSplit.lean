import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.ComplexScalar

namespace OAI

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def ProportionalProjectionSupply {I : Type*} (Γ : I → TracialState D) : Prop :=
  ∀ (q : D), IsStarProjection q → ∀ t : ℝ, t ∈ Set.Icc 0 1 →
    ∃ e : D, IsStarProjection e ∧ e ≤ q ∧
      ∀ i, (Γ i).functional e = (t:ℂ)*(Γ i).functional q

lemma finite_coefficient_split {I : Type*} (Γ : I → TracialState D)
    (hsupply : SpectralProjectionSupply Γ) (hdivide : ProportionalProjectionSupply Γ)
    {q : D} (hq : IsStarProjection q) {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    (F : Finset D) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧ e ≤ q ∧ ∀ b ∈ F, ∀ i,
      ‖(Γ i).functional (e*b)-(s:ℂ)*(Γ i).functional (q*b)‖ < ε := by
  classical
  let γ := ε/4
  let M := 1+∑ b ∈ F, ‖b‖
  have hM : 0 < M := by
    have := Finset.sum_nonneg (fun b (_ : b ∈ F) => norm_nonneg b)
    dsimp [M]; linarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  let δ := ε/(4*M)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨P,hP,hPi⟩ := finite_complex_scalar Γ hsupply F hγ hδ q hq
  choose E hE hEP hEt using fun j : P.Index => hdivide (P.piece j) (P.projection j) s hs
  have horth : Pairwise (fun i j => E i*E j=0) := by
    intro i j hij
    exact mul_eq_zero_of_supports ((hE i).le_iff_mul_eq_left (P.projection i) |>.mp (hEP i))
      ((hE j).le_iff_mul_eq_right (P.projection j) |>.mp (hEP j)) (P.orthogonal hij)
  let e := ∑ j : P.Index, E j
  have he : IsStarProjection e := orthogonal_projection_sum Finset.univ E
    (fun j _ => hE j) (fun _ _ _ _ hij => horth hij)
  have heP : e ≤ P.total := Finset.sum_le_sum (fun j _ => hEP j)
  refine ⟨e,he,heP.trans P.total_le,?_⟩
  intro b hb i
  let τ := Γ i
  have hbM : ‖b‖ ≤ M := by
    have := Finset.single_le_sum (f := fun b : D => ‖b‖) (fun b _ => norm_nonneg b) hb
    dsimp [M]; linarith
  have hte : ∑ j : P.Index, (τ.functional (E j)).re = (τ.functional e).re := by
    simp only [e,map_sum,Complex.re_sum]
  have htP : ∑ j : P.Index, (τ.functional (P.piece j)).re = (τ.functional P.total).re := by
    simp only [ProjectionPacking.total,map_sum,Complex.re_sum]
  have hmass : (τ.functional e).re + s*(τ.functional P.total).re ≤ 2 := by
    have hP0 := (τ.functional.map_nonneg P.total_projection.nonneg).1
    have hP1 := trace_projection_le_one τ P.total_projection
    have he1 := trace_projection_le_one τ he
    nlinarith [hs.1,hs.2]
  have herr (j : P.Index) :
      ‖τ.functional (E j*b)-(s:ℂ)*τ.functional (P.piece j*b)‖ ≤
        γ*((τ.functional (E j)).re+s*(τ.functional (P.piece j)).re) := by
    obtain ⟨α,hα⟩ := hP b hb j
    have h := scalar_splitting_error τ (hE j) (P.projection j) (hEP j) hs.1 b α hα
    simpa only [τ,hEt j i,sub_self,norm_zero,mul_zero,add_zero] using h
  have hsum : ‖τ.functional (e*b)-(s:ℂ)*τ.functional (P.total*b)‖ ≤ γ*2 := by
    have heq : τ.functional (e*b)-(s:ℂ)*τ.functional (P.total*b) =
        ∑ j : P.Index, (τ.functional (E j*b)-(s:ℂ)*τ.functional (P.piece j*b)) := by
      simp only [e,ProjectionPacking.total,Finset.sum_mul,map_sum,Finset.mul_sum,Finset.sum_sub_distrib]
    rw [heq]
    calc
      _ ≤ ∑ j : P.Index, ‖τ.functional (E j*b)-(s:ℂ)*τ.functional (P.piece j*b)‖ := norm_sum_le _ _
      _ ≤ ∑ j : P.Index, γ*((τ.functional (E j)).re+s*(τ.functional (P.piece j)).re) :=
        Finset.sum_le_sum (fun j _ => herr j)
      _ = γ*((τ.functional e).re+s*(τ.functional P.total).re) := by
        rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum,hte,htP]
      _ ≤ γ*2 := mul_le_mul_of_nonneg_left hmass hγ.le
  have hres : ‖(s:ℂ)*τ.functional (P.residual*b)‖ ≤ M*δ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
    have ht0 := (τ.functional.map_nonneg (P.residual_projection hq).nonneg).1
    have ht := hPi i
    calc
      _ ≤ s*(‖b‖*(τ.functional P.residual).re) := mul_le_mul_of_nonneg_left
        (trace_norm_projection_mul_le τ (P.residual_projection hq) b) hs.1
      _ ≤ 1*(M*δ) := mul_le_mul hs.2
          (mul_le_mul hbM ht (by simpa using ht0) hM.le)
          (mul_nonneg (norm_nonneg b) (by simpa using ht0)) zero_le_one
      _ = M*δ := one_mul _
  have heq : τ.functional (e*b)-(s:ℂ)*τ.functional (q*b) =
      (τ.functional (e*b)-(s:ℂ)*τ.functional (P.total*b))-
        (s:ℂ)*τ.functional (P.residual*b) := by
    simp only [ProjectionPacking.residual,sub_mul,map_sub]
    ring
  rw [heq]
  have hδM : M*δ=ε/4 := by dsimp [δ]; field_simp
  exact (norm_sub_le _ _).trans (add_le_add hsum hres) |>.trans_lt (by rw [hδM]; dsimp [γ]; linarith)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
local notation "D₀" => FamilyUltrapower (fun τ : TracialState A => τ) U
local notation "Λ" => familyLimitTrace (fun τ : TracialState A => τ) U

include hfree in

theorem coefficient_split (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hcmp : StrictComparison A)
    {q : D₀} (hq : IsStarProjection q) {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    (F : Finset D₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D₀, IsStarProjection e ∧ e ≤ q ∧ ∀ b ∈ F, ∀ i : ℕ → TracialState A,
      ‖(Λ i).functional (e*b)-(s:ℂ)*(Λ i).functional (q*b)‖ < ε := by
  exact finite_coefficient_split Λ
    (fun h hh hhn α hα hα1 => projection_supply U hfree hsimple hinf hcmp h hh hhn α hα hα1)
    (fun q hq t ht => proportional_subprojection U hfree hsimple hinf hcmp hq ht) hq hs F hε

end DirectComparison

namespace DirectComparison
open Filter
open scoped Topology

lemma diagonal_choice (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
    (P : ℕ → ℕ → Prop) (hP : ∀ m, ∀ᶠ k in (U : Filter ℕ), P m k) :
    ∃ j : ℕ → ℕ, Tendsto j (U : Filter ℕ) atTop ∧
      ∀ᶠ k in (U : Filter ℕ), P (j k) k := by
  classical
  let j : ℕ → ℕ := fun k => Nat.findGreatest (fun n => ∀ m ≤ n, P m k) k
  have hfin (n : ℕ) : ∀ᶠ k in (U : Filter ℕ), ∀ m ≤ n, P m k := by
    have h := (eventually_all_finset (Finset.range (n+1))).mpr (fun m _ => hP m)
    filter_upwards [h] with k hk
    intro m hm
    exact hk m (Finset.mem_range.mpr (by omega))
  refine ⟨j,?_,?_⟩
  · apply tendsto_atTop.mpr
    intro n
    filter_upwards [hfin n, hfree (eventually_ge_atTop n)] with k hk hnk
    exact Nat.le_findGreatest hnk hk
  · filter_upwards [hfin 0] with k hk
    exact (Nat.findGreatest_spec (P := fun n => ∀ m ≤ n, P m k) (Nat.zero_le k) hk) (j k) le_rfl

end DirectComparison
end

end OAI
