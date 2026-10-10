import Mathlib
import OAI.Probability.CoordinateSweeps.BaseCase
import OAI.Probability.CoordinateSweeps.SparseBound

namespace OAI

/-!
All definitions are finite and use the source's ordinary probability and trace
normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! The alternating placement kernel from 04-sparse:eq7.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/- Necessary shared-line polynomial expansion for the sparse conditional main.
A variable names a LINE, not a particle. The tensor moment functional is merely
linear, never multiplicative when two factors use the same line. -/
noncomputable section
open scoped BigOperators
open MvPolynomial

/- The analytic light-line obligation 04-sparse.tex (11).  The distribution
is exactly Mathlib's Gamma(shape, unit rate). -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators

/- Finite subset rearrangements needed for the actual good/non-good path
alternation in source04:eq10. -/
noncomputable section
open scoped BigOperators

/- Required top-placement compression for the conditional main. The top space
is the annihilator of all functions depending on a proper set of coordinates.
This is the exact top level used in source04 around eq7. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

noncomputable section
universe u v
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators

open scoped Matrix.Norms.L2Operator

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CoordinateSweeps.SparseScalar
structure SizeReady (s : ℝ) : Prop where
  two : 2 ≤ s
  logpow : Real.log s ≤ s^(theta/4)
  powtwo : 2 ≤ s^(theta/4)
  powB : (B0+1:ℝ) ≤ s^(theta/2)
  count : 4/s^(1/(4*(B0:ℝ))) ≤ theta/(64*B0)
  absorb : Real.log (1+2*(B0:ℝ))+Real.log 2 ≤ xi*Real.log s
  eta : s^(-xi) ≤ 1/8
  prefactor : uniformRate ≤ xi*Real.log s/16
  logtwo : Real.log 2 ≤ xi*Real.log s/8
lemma eventually_sizeReady : ∀ᶠ s : ℝ in atTop, SizeReady s := by
  have hp := eventually_power_gt xi 8 (by norm_num [xi])
  filter_upwards [eventually_sparse_requirements,eventually_prefactor_small,hp,eventually_ge_atTop (2:ℝ)]
    with s hs hf hp h2
  refine ⟨h2,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,?_,?_,hf,hs.2.2.2.2.2.2⟩
  · simpa only [add_comm] using hs.2.2.2.2.2.1
  · rw [Real.rpow_neg (by linarith : 0 ≤ s)]
    simpa only [one_div] using (inv_le_inv₀ (by linarith : 0<s^xi) (by norm_num : (0:ℝ)<8)).mpr hp.le
structure ScaleReady (r : ℕ) : Prop where
  two : 2 ≤ r
  logone : 1 ≤ (r:ℝ)*Real.log 2
  absorb : 3*Real.log 2+2*(K0+1+Real.log 4) ≤ theta*((r:ℝ)*Real.log 2)/8
  size : ∀ s : ℝ, (2:ℝ)^r ≤ s → SizeReady s
lemma eventually_scaleReady : ∀ᶠ r : ℕ in atTop, ScaleReady r := by
  obtain ⟨S,hS⟩ := eventually_atTop.mp eventually_sizeReady
  have ht : Tendsto (fun r : ℕ => (r:ℝ)*Real.log 2) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos (Real.log_pos (by norm_num))).mpr tendsto_natCast_atTop_atTop
  have h1 := ht.eventually (eventually_ge_atTop (1:ℝ))
  have h2 := ht.eventually (eventually_ge_atTop ((3*Real.log 2+2*(K0+1+Real.log 4))*8/theta))
  have hp : Tendsto (fun r : ℕ => (2:ℝ)^r) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [h1,h2,hp.eventually (eventually_ge_atTop S),eventually_ge_atTop (2:ℕ)] with r hr1 hr2 hrS hr
  refine ⟨hr,hr1,?_,fun s hs => hS s (hrS.trans hs)⟩
  have hh := mul_le_mul_of_nonneg_right hr2 (by norm_num [theta] : 0 ≤ theta)
  have hth : theta ≠ 0 := by norm_num [theta]
  rw [div_mul_cancel₀ _ hth] at hh
  nlinarith
/- Positive slack used by the uniform finite real perturbation. -/
def slack (s : ℝ) : ℝ :=
  if 1 < s then s ^ (-((2 : ℕ) : ℝ) * rho * s) * (s ^ rho - 1) else 1
lemma slack_pos (s : ℝ) : 0 < slack s := by
  unfold slack
  split_ifs with hs
  · exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (sub_pos.mpr
      (Real.one_lt_rpow hs (by norm_num [rho])))
  · norm_num
lemma slack_le_gap {s : ℝ} (hs : 1<s) {k : ℕ} (hk : 1 ≤ k) (hks : (k : ℝ) ≤ s) :
    slack s ≤ s^(-rho*k)-s^(-2*rho*k) := by
  have hs0 : 0<s := by linarith
  have hr : 0<rho := by norm_num [rho]
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  rw [slack,ite_eq_left hs]
  have h1 : s^(-2*rho*s) ≤ s^(-2*rho*k) := Real.rpow_le_rpow_of_exponent_le hs.le (by nlinarith)
  have h2 : s^rho ≤ s^(rho*k) := Real.rpow_le_rpow_of_exponent_le hs.le (by nlinarith)
  have h3 : 0 ≤ s^rho-1 := sub_nonneg.mpr (Real.one_le_rpow hs.le hr.le)
  apply (mul_le_mul h1 (sub_le_sub_right h2 1) h3 (Real.rpow_nonneg hs0.le _)).trans_eq
  rw [mul_sub,mul_one,← Real.rpow_add hs0]
  congr 2
  ring
end CoordinateSweeps.SparseScalar
namespace CoordinateSweeps.Grid
open SparseScalar
lemma pow_r_le_size (G : Grid) {r : ℕ} (hG : G.Allowed r) : (2:ℝ)^r ≤ G.size := by
  have hb : (1:ℝ)≤G.b := by exact_mod_cast G.positive
  have hl := (le_mul_of_one_le_left (by positivity : 0≤(r:ℝ)*Real.log 2) hb).trans (G.log_size_lower hG)
  rw [pow_two_exp]
  exact (Real.exp_le_exp.mpr hl).trans_eq (Real.exp_log (by exact_mod_cast G.size_pos))
lemma sizeReady (G : Grid) {r : ℕ} (hr : ScaleReady r) (hG : G.Allowed r) : SizeReady G.size :=
  hr.size _ (G.pow_r_le_size hG)
lemma sparse_uniform_room (G : Grid) {r h k : ℕ} (hr : ScaleReady r) (hG : G.Allowed r)
    (hsp : ((h+k:ℕ):ℝ)≤(G.size:ℝ)^(1-theta)) (j : Fin G.b) :
    h+k+Fintype.card (G.Line j)<G.size := by
  have hs := G.sizeReady hr hG
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  have hhalf : 2*((h+k:ℕ):ℝ)≤G.size := by
    calc
      _ ≤ (G.size:ℝ)^(theta/4)*(G.size:ℝ)^(1-theta) :=
        mul_le_mul hs.powtwo hsp (Nat.cast_nonneg _) (Real.rpow_nonneg hs0.le _)
      _ = (G.size:ℝ)^(theta/4+(1-theta)) := (Real.rpow_add hs0 _ _).symm
      _ ≤ (G.size:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le (by linarith [hs.two]) (by norm_num [theta])
      _ = _ := Real.rpow_one _
  have hm : 4≤2^G.bits j := (by norm_num : 4≤2^2).trans (Nat.pow_le_pow_right (by norm_num) (hr.two.trans (hG j).1))
  have hline := G.card_line_mul j
  have hquart : 4*Fintype.card (G.Line j)≤G.size := by nlinarith
  have hq : 4*(Fintype.card (G.Line j):ℝ)≤G.size := by exact_mod_cast hquart
  have hout : (((h+k+Fintype.card (G.Line j)):ℕ):ℝ)<G.size := by push_cast at hhalf ⊢; nlinarith
  exact_mod_cast hout
lemma sparse_many_room (G : Grid) {r h k : ℕ} (hr : ScaleReady r) (hG : G.Allowed r)
    (hb : B0≤G.b) (hsp : ((h+k:ℕ):ℝ)≤(G.size:ℝ)^(1-theta)) (j : Fin G.b) :
    h+k<Fintype.card (G.Line j) := by
  have hs := G.sizeReady hr hG
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  have hp : ((h+k:ℕ):ℝ)*(2^G.bits j:ℝ)<G.size := by
    calc
      _ ≤ (G.size:ℝ)^(1-theta)*(G.size:ℝ)^(theta/4) :=
        mul_le_mul hsp (G.coordinate_size_many (by have hh := hr.two; omega) hG hb j) (by positivity) (Real.rpow_nonneg hs0.le _)
      _ = (G.size:ℝ)^(1-theta+theta/4) := (Real.rpow_add hs0 _ _).symm
      _ < (G.size:ℝ)^1 := Real.rpow_lt_rpow_of_exponent_lt (by linarith [hs.two]) (by norm_num [theta])
      _ = _ := Real.rpow_one _
  have hpN : (h+k)*(2^G.bits j)<G.size := by exact_mod_cast hp
  rw [← G.card_line_mul j,mul_comm (2^G.bits j)] at hpN
  exact (Nat.mul_lt_mul_right (by positivity)).mp hpN
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
open SparseScalar
variable {G : Grid} {h k r : ℕ} (H : G.Holes h)
lemma lineLaw_zero (d : ℕ) : lineLaw d 0 (by norm_num) (by norm_num) = FiniteLaw.uniform _ := by
  ext g
  simp [lineLaw, FiniteLaw.mix]
lemma sparse_uniform_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    (hb : G.b ≤ B0) (hk : 1 ≤ k) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0)))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    (hnof : ∀ A : Finset (H.FreeAt 0), A.card < k → ∀ v : Fin ρ.dimension → ℂ,
      (∀ g : Equiv.Perm (H.FreeAt 0), (∀ a ∈ A, g a=a) → ρ.asRepresentation g v=v) → v=0) :
    ‖H.conditionalAverage hf 0 (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-2*rho*k) := by
  have hs := G.sizeReady hr hG
  have hhS := H.sparse_uniform_HS_bound hf hG hb hk hh hs.two hsp hs.powtwo hs.powB hs.count
    hs.absorb hs.eta hs.prefactor hs.logtwo
  have hn := H.conditional_norm_le_placementHS hf (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)≤1)
    ρ u hu x₀ hfixed hnof
  simp only [lineLaw_zero] at hn
  apply hn.trans ((Real.sqrt_le_sqrt hhS).trans_eq ?_)
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by positivity : (0:ℝ)≤G.size)]
  congr 1
  norm_num [xi,rho]
  ring
lemma sparse_many_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    (hb : B0 ≤ G.b) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2:ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0)))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    (hnof : ∀ A : Finset (H.FreeAt 0), A.card < k → ∀ v : Fin ρ.dimension → ℂ,
      (∀ g : Equiv.Perm (H.FreeAt 0), (∀ a ∈ A, g a=a) → ρ.asRepresentation g v=v) → v=0) :
    ‖H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-rho*k) := by
  have hs := G.sizeReady hr hG
  have hhS := H.sparse_many_HS_bound hf (by have hh:=hr.two; omega) hG hb hr.logone hr.absorb hh hs.logpow hsp hz hz' hlo hhi
  apply (H.conditional_norm_le_placementHS hf hz hz' ρ u hu x₀ hfixed hnof).trans
    ((Real.sqrt_le_sqrt hhS).trans ?_)
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by positivity : (0:ℝ)≤G.size)]
  apply Real.rpow_le_rpow_of_exponent_le (by linarith [hs.two])
  have hk0 := (Nat.cast_nonneg k : (0:ℝ)≤k)
  norm_num [theta,rho]
  nlinarith
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.SparseDimension
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
structure Level (ρ : UnitaryIrrep (Equiv.Perm Ω)) (k : ℕ) where
  flipped : Bool
  vector : Fin ρ.dimension → ℂ
  nonzero : vector ≠ 0
  placement : Fin k ↪ Ω
  fixed : ∀ g : Equiv.Perm Ω, (∀ i, g (placement i)=placement i) →
    (if flipped then signTwist ρ.asRepresentation else ρ.asRepresentation) g vector=vector
  minimal : ∀ A : Finset Ω, A.card < k → ∀ v : Fin ρ.dimension → ℂ,
    (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a=a) →
      (if flipped then signTwist ρ.asRepresentation else ρ.asRepresentation) g v=v) → v=0
lemma exists_level (ρ : UnitaryIrrep (Equiv.Perm Ω)) :
    ∃ k t : ℕ, k ≤ 2*t ∧ 2^t ≤ ρ.dimension ∧ ρ.dimension ≤ (Fintype.card Ω)^k ∧
      k ≤ Fintype.card Ω ∧ Nonempty (Level ρ k) := by
  obtain ⟨ε,k,t,A,u,hA,hk,ht,hd,hu,hf,hn⟩ := exists_minimal_fixed_vector ρ.asRepresentation
  have hcard : Fintype.card A=k := by simpa using hA
  let eA : A ≃ Fin k := Fintype.equivFinOfCardEq hcard
  let x : Fin k ↪ Ω := eA.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ A))
  refine ⟨k,t,hk,by simpa using ht,by simpa using hd,?_,⟨⟨ε,u,hu,x,?_,hn⟩⟩⟩
  · rw [← hA]
    exact Finset.card_le_univ A
  · intro g hg
    apply hf g
    intro a ha
    have hh := hg (eA ⟨a,ha⟩)
    simpa [x] using hh
omit [DecidableEq Ω] in
lemma level_log_bounds (ρ : UnitaryIrrep (Equiv.Perm Ω)) {s k t : ℕ}
    (hs : 0 < s) (hΩ : Fintype.card Ω ≤ s) (hk : k ≤ 2*t)
    (ht : 2^t ≤ ρ.dimension) (hd : ρ.dimension ≤ (Fintype.card Ω)^k) :
    Real.log ρ.dimension ≤ k*Real.log s ∧ (k:ℝ) ≤ 4*Real.log ρ.dimension := by
  have hD : (0:ℝ)<ρ.dimension := by exact_mod_cast ρ.positive
  have hs0 : (0:ℝ)<s := by exact_mod_cast hs
  constructor
  · have hh : (ρ.dimension:ℝ) ≤ (s:ℝ)^k := by exact_mod_cast hd.trans (Nat.pow_le_pow_left hΩ k)
    simpa only [Real.log_pow] using Real.log_le_log hD hh
  · have htt : (2:ℝ)^t ≤ ρ.dimension := by exact_mod_cast ht
    have hh := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^t) htt
    rw [Real.log_pow] at hh
    have hlog : (1/2:ℝ) ≤ Real.log 2 := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
      norm_num at hh
      linarith
    have hk' : (k:ℝ) ≤ 2*t := by exact_mod_cast hk
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t : (0:ℝ)≤t)]
end CoordinateSweeps.SparseDimension

namespace CoordinateSweeps.Grid.Holes
open SparseScalar SparseDimension
variable {G : Grid} {h k r : ℕ} (H : G.Holes h)
lemma level_uniform_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    (hb : G.b ≤ B0) (hk : 1 ≤ k) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (L : Level ρ k) :
    ‖H.conditionalAverage hf 0 (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-2*rho*k) := by
  cases he : L.flipped
  · apply H.sparse_uniform_norm hr hG hf hb hk hh hsp ρ L.vector L.nonzero L.placement
    · simpa [he] using L.fixed
    · simpa [he] using L.minimal
  · have hz := H.conditional_column_zero_uniform hf ρ L.vector L.nonzero L.placement
      (by simpa [he] using L.fixed) ⟨0,G.positive⟩
      (G.sparse_uniform_room hr hG hsp _)
    rw [hz,norm_zero]
    positivity
lemma level_many_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    (hb : B0 ≤ G.b) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2:ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (L : Level ρ k) :
    ‖H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-rho*k) := by
  cases he : L.flipped
  · apply H.sparse_many_norm hr hG hf hb hh hsp hz hz' hlo hhi ρ L.vector L.nonzero L.placement
    · simpa [he] using L.fixed
    · simpa [he] using L.minimal
  · have hz := H.conditional_column_zero_many hf hz hz' ρ L.vector L.nonzero L.placement
      (by simpa [he] using L.fixed) ⟨0,G.positive⟩
      (by have hh:=hr.two; have hg:=(hG ⟨0,G.positive⟩).1; omega)
      (G.sparse_many_room hr hG hb hsp _)
    rw [hz,norm_zero]
    positivity
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
lemma baseZeta_le_inv_card {r d : ℕ} (hd : d ≤ 2*r) :
    baseZeta r ≤ (Fintype.card (Equiv.Perm (Cube d)) : ℝ)⁻¹ := by
  have hB := baseWidth_one_le r
  have hC := single_card_le_baseWidth hd
  have hC0 : (0:ℝ)<Fintype.card (Equiv.Perm (Cube d)) := by exact_mod_cast Fintype.card_pos
  unfold baseZeta
  rw [one_div]
  exact (inv_le_inv₀ (by positivity) hC0).mpr (by nlinarith)
lemma lineLaw_base_bounds {r d : ℕ} (hd : d ≤ 2*r) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r)
    (g : Equiv.Perm (Cube d)) :
    (1/2:ℝ)*FiniteLaw.uniform _ g ≤ lineLaw d z hz (hz'.trans (baseZeta_le_half r) |>.trans (by norm_num)) g ∧
      lineLaw d z hz (hz'.trans (baseZeta_le_half r) |>.trans (by norm_num)) g ≤ 2*FiniteLaw.uniform _ g :=
  FiniteLaw.mix_uniform_between (binaryLaw d) hz (hz'.trans (baseZeta_le_half r))
    (hz'.trans (baseZeta_le_inv_card hd)) g

def SparsePerturb (r : ℕ) (zStar : ℝ) : Prop :=
  0 < zStar ∧ zStar ≤ baseZeta r ∧ ∀ G : Grid, G.b ≤ SparseScalar.B0 → G.Allowed r →
    ∀ z ∈ Set.Icc 0 zStar, ∀ E : Finset G.Choices, E.Nonempty →
      G.eventDistance E z < SparseScalar.slack G.size
lemma exists_sparsePerturb (r : ℕ) : ∃ zStar, SparsePerturb r zStar := by
  obtain ⟨δ,hδ,hδh,hd⟩ := Grid.bounded_event_interval SparseScalar.B0 r
    (fun G => SparseScalar.slack G.size) (fun _ => SparseScalar.slack_pos _)
  refine ⟨min δ (baseZeta r),lt_min hδ (baseZeta_pos r),min_le_right _ _,?_⟩
  intro G hb hG z hz E hE
  exact hd G hb (fun j => (hG j).2) z ⟨hz.1,hz.2.trans (min_le_left _ _)⟩ E hE
end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
open SparseScalar SparseDimension
variable {G : Grid} {h k r : ℕ} (H : G.Holes h)
lemma level_sparse_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z ∈ Set.Icc 0 zStar)
    (hk : 1 ≤ k) (hks : k ≤ G.size) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (L : Level ρ k) :
    ‖H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-rho*k) := by
  have hzB := hz.2.trans hζ.2.1
  have hz1 : z ≤ 1 := (hzB.trans (baseZeta_le_half r)).trans (by norm_num)
  by_cases hb : B0 ≤ G.b
  · apply H.level_many_norm hr hG hf hb hh hsp hz.1 hz1
    · exact fun j g => (lineLaw_base_bounds (hG j).2 hz.1 hzB g).1
    · exact fun j g => (lineLaw_base_bounds (hG j).2 hz.1 hzB g).2
    · exact L
  · have hb' : G.b ≤ B0 := by omega
    have hU := H.level_uniform_norm hr hG hf hb' hk hh hsp ρ L
    have hP := H.conditionalAverage_perturb_bound hf z (ρ.pullback H.stabilizerFreeEquiv)
    have hdist := hζ.2.2 G hb' hG z hz H.event (H.event_nonempty hf)
    have hS := G.sizeReady hr hG
    have hgap := slack_le_gap (by linarith [hS.two] : (1:ℝ)<G.size) hk (by exact_mod_cast hks)
    linarith
end CoordinateSweeps.Grid.Holes
end
end
end
end
end
end
end
end
end

open scoped Matrix.Norms.L2Operator

end OAI
