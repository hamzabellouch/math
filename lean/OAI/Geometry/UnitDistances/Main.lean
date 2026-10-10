import OAI.Geometry.UnitDistances.Obstruction

namespace OAI

namespace PlanarUnitDistances.IncidenceDiagonal
open Filter Finset IncidenceSequence IncidenceScale IncidenceBook PowerGrowth
open scoped Classical
noncomputable section

def delta (n : ℕ) : ℝ := 1/(3*((n:ℝ)+1))
lemma delta_pos (n : ℕ) : 0<delta n := by unfold delta; positivity
lemma delta_le (n : ℕ) : delta n≤1/3 := by
  unfold delta
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]
lemma delta_limit : Tendsto delta atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1/(3*((n:ℝ)+1))) atTop (nhds 0)
  convert Sequence.accuracy_limit.div_const 3 using 1 <;> simp [div_eq_mul_inv,mul_comm]

structure Data (s : Sequence) where
  f : ℕ → ℕ
  cofinal : Tendsto f atTop atTop
  a : ℕ → BudgetParameters.Params
  R : ∀n,Realization s (a n) (f n)
  J : ℕ → ℝ
  positive : ∀n,0<J n
  large : ∀n : ℕ,(n:ℝ)+1≤J n
  dense : ∀n,s.t (f n)^(2-1/((n:ℝ)+1))≤(IncidenceSelected.pairs (R n) (J n) (delta n)).card
  popular : ∀n,2≤IncidencePopular.k s (f n)

theorem exists_data (s : Sequence) : Nonempty (Data s) := by
  obtain ⟨c,hc,h⟩ := IncidenceSelected.choose s
  choose a b hb h using fun n => h (delta n) (delta_pos n) (delta_le n)
  have hh (n : ℕ) : ∀ᶠi in atTop,∃R : Realization s (a n) i,∃J : ℝ,
      0<J ∧ (n:ℝ)+1≤J ∧
      s.t i^(2-1/((n:ℝ)+1))≤(IncidenceSelected.pairs R J (delta n)).card ∧
      2≤IncidencePopular.k s i := by
    filter_upwards [h n,(s.wedge_power.const_mul s.tendsto (hb n)) (1/((n:ℝ)+1)) (by positivity),
      (scale_limit s).eventually_ge_atTop (2*((n:ℝ)+1)/c),IncidencePopular.k_large s] with i hi hpow hscale hk
    obtain ⟨R,J,hJ,hJ',hcount⟩ := hi
    have hc' := (div_le_iff₀ hc).mp hscale
    exact ⟨R,J,hJ,by nlinarith,hpow.trans hcount,hk⟩
  obtain ⟨f,hf,h⟩ := PowerGrowth.diagonal hh
  choose R J hJ hj hd hk using h
  exact ⟨⟨f,hf,a,R,J,hJ,hj,hd,hk⟩⟩

namespace Data
variable {s : Sequence} (D : Data s)
def t (n : ℕ) := s.t (D.f n)
def P (n : ℕ) := IncidencePopular.points s (D.f n)
def E (n : ℕ) := IncidenceComplex.edge (D.R n) (D.J n) (delta n)
def K (n : ℕ) : Type := (model s (D.f n)).field
instance (n : ℕ) : Field (D.K n) := inferInstanceAs (Field (model s (D.f n)).field)
instance (n : ℕ) : NumberField (D.K n) := inferInstanceAs (NumberField (model s (D.f n)).field)
instance (n : ℕ) : IsGalois ℚ (D.K n) := inferInstanceAs (IsGalois ℚ (model s (D.f n)).field)
def e (n : ℕ) : D.K n →+* ℂ := (model s (D.f n)).field.val.toRingHom
def ell (n : ℕ) : ℂ → ℂ → D.K n := IncidenceComplex.label (D.R n) (D.J n) (delta n)
lemma t_limit : Tendsto D.t atTop atTop := s.tendsto.comp D.cofinal
lemma J_limit : Tendsto D.J atTop atTop :=
  tendsto_atTop_mono (fun n => (by linarith [D.large n] : (n:ℝ)≤D.J n)) tendsto_natCast_atTop_atTop
lemma card_power : Upper atTop D.t (fun n => ((D.P n).card:ℝ)) 1 := by
  intro ε hε
  filter_upwards [D.cofinal.eventually (s.cardP_power ε hε)] with n hn
  simpa only [P,t,IncidencePopular.points_card] using hn
lemma edge_power : Lower atTop D.t
    (fun n => (GenericGrid.edges (fun n (p r : D.P n) => D.E n p r) n).card) 2 := by
  intro ε hε
  filter_upwards [Sequence.accuracy_limit.eventually_le_const hε] with n hn
  have ht : 1 ≤ s.t (D.f n) := by linarith [s.large (D.f n),Nat.cast_nonneg (α:=ℝ) (D.f n)]
  have h := (Real.rpow_le_rpow_of_exponent_le ht (by linarith : 2-ε≤2-1/((n:ℝ)+1))).trans (D.dense n)
  rw [←IncidenceComplex.card (D.R n) (D.J n) (delta n)] at h
  dsimp only [GenericGrid.edges,E,P,t]
  convert h using 1
  all_goals congr 8
lemma residual_small : (fun n => 4*delta n*D.J n)=o[atTop] D.J := by
  apply (Asymptotics.isLittleO_iff_tendsto (fun n h => (D.positive n).ne' h |>.elim)).mpr
  have h := delta_limit.const_mul 4
  convert h using 1
  · ext n
    exact mul_div_cancel_right₀ (4*delta n) (D.positive n).ne'
  · simp
end Data
end
end PlanarUnitDistances.IncidenceDiagonal

namespace PlanarUnitDistances.IncidenceDiagonal
open Filter PowerGrowth IncidenceSequence
open scoped Classical
noncomputable section
namespace Data
variable {s : Sequence} (D : Data s)
lemma hypotheses (U : Ultrafilter ℕ) (hU : (U:Filter ℕ)≤atTop) :
    AlgebraicObstruction.Hypotheses U D.t D.J D.P D.E D.K D.e D.ell := by
  constructor
  · intro n p hp r hr he
    exact IncidenceComplex.nonzero (D.R n) (D.positive n) (delta_pos n).le (delta_le n)
      ⟨p,hp⟩ ⟨r,hr⟩ he
  · intro n p hp r hr he
    exact IncidenceComplex.distance (D.R n) (D.positive n) (delta_pos n).le (delta_le n)
      ⟨p,hp⟩ ⟨r,hr⟩ he
  · refine ⟨1/3,by norm_num,?_⟩
    intro n p hp r hr he
    have hh := IncidenceComplex.large (D.R n) (D.positive n) (delta_pos n).le (delta_le n) ⟨p,hp⟩ ⟨r,hr⟩ he
    change (1/3)*D.J n≤WeightedAbsoluteValues.exactHeight (IncidenceScale.model s (D.f n)).field
      (IncidenceComplex.label (D.R n) (D.J n) (delta n) p r)
    convert hh using 1; ring
  · refine ⟨fun n => 4*delta n*D.J n,D.residual_small.mono hU,?_⟩
    intro n p hp p' hp' r hr r' hr' h₁ h₂ h₃ h₄
    exact IncidenceComplex.rectangle (D.R n) (D.positive n) (delta_pos n).le (delta_le n)
      ⟨p,hp⟩ ⟨p',hp'⟩ ⟨r,hr⟩ ⟨r',hr'⟩ h₁ h₂ h₃ h₄
  · intro n p hp r hr he c hc
    exact IncidenceComplex.no_circle (D.R n) (D.popular n) ⟨p,hp⟩ ⟨r,hr⟩ he c hc

end Data

theorem impossible (s : Sequence) : False := by
  obtain ⟨D⟩ := exists_data s
  let U := Filter.hyperfilter ℕ
  have hU : (U:Filter ℕ)≤atTop := Nat.hyperfilter_le_atTop
  exact AlgebraicObstruction.no_rectangles U hU D.t D.J (D.t_limit.mono_left hU)
    (D.J_limit.mono_left hU) D.P (fun ε hε => hU (D.card_power ε hε))
    D.E (fun ε hε => hU (D.edge_power ε hε)) D.K D.e D.ell (D.hypotheses U hU)
end
end PlanarUnitDistances.IncidenceDiagonal

namespace PlanarUnitDistances
open Filter PowerGrowth

theorem main : ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < (4 : ℝ) / 3 ∧
    ∀ n : ℕ, (u n : ℝ) ≤ C * (n : ℝ) ^ β := by
  by_contra h
  obtain ⟨t,X,ht,ht1,hX0,_,hX,hE,hAlg⟩ := counterexample_power_sequence h
  obtain ⟨s⟩ := IncidenceSequence.diagonal_sequence ht ht1 hX0 hX hE hAlg
  exact IncidenceDiagonal.impossible s
end PlanarUnitDistances

end OAI
