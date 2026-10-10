import OAI.Geometry.LatticeCovering.BrokenCircuits

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.RogersPreparation
open Filter Topology

lemma eventually_const_mul_rpow_lt {a : ℝ} (ha : a<1) (A : ℝ) :
    ∀ᶠ p : ℕ in atTop, A * (p : ℝ)^a < p := by
  have ht : Tendsto (fun p : ℕ => A * (p : ℝ)^(a-1)) atTop (𝓝 0) := by
    have h : Tendsto (fun p : ℕ => (p : ℝ)^(a-1)) atTop (𝓝 0) := by
      have hcast : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def,neg_sub] using
        (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp hcast
    simpa only [mul_zero] using h.const_mul A
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop 1] with p hp hp1
  have hpR : (0:ℝ)<p := by exact_mod_cast hp1
  have he : (p : ℝ)^a = (p : ℝ)^(a-1)*(p : ℝ) := by
    calc
      _ = (p : ℝ)^((a-1)+1) := by congr 1; ring
      _ = (p : ℝ)^(a-1)*(p : ℝ)^(1:ℝ) := Real.rpow_add hpR _ _
      _ = _ := by rw [Real.rpow_one]
  rw [he,←mul_assoc]
  simpa only [one_mul] using mul_lt_mul_of_pos_right hp hpR

lemma eventually_subcritical_minor_bound {d k : ℕ} (hk : k<d) {C : ℝ} (hC : 1≤C) :
    ∀ᶠ p : ℕ in atTop,
      1 ≤ C * (p : ℝ)^((d : ℝ)⁻¹) ∧
      (k.factorial : ℝ) * (C * (p : ℝ)^((d : ℝ)⁻¹))^k < p := by
  have hd : (0:ℝ)<d := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  have ha : (d : ℝ)⁻¹*k<1 := by
    rw [mul_comm,←div_eq_mul_inv,div_lt_one hd]
    exact_mod_cast hk
  filter_upwards [eventually_const_mul_rpow_lt ha ((k.factorial : ℝ)*C^k),
    eventually_ge_atTop 1] with p hp hp1
  have hpR : (1:ℝ)≤p := by exact_mod_cast hp1
  constructor
  · exact one_le_mul_of_one_le_of_one_le hC
      (Real.one_le_rpow hpR (inv_nonneg.mpr hd.le))
  · rw [mul_pow,←Real.rpow_mul_natCast (by positivity : (0:ℝ)≤p),←mul_assoc]
    exact hp


end SingleLatticeCovering.RogersPreparation

namespace SingleLatticeCovering.ConvexGrid
open MeasureTheory Filter Topology RogersPreparation AffineCircuit
open scoped BigOperators

def primeScale (d p : ℕ) : ℝ := (p:ℝ)^((d:ℝ)⁻¹)

lemma primeScale_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (primeScale d) atTop atTop :=
  (tendsto_rpow_atTop (inv_pos.mpr (by exact_mod_cast hd))).comp tendsto_natCast_atTop_atTop

lemma primeScale_pos {d p : ℕ} (hp : 0 < p) : 0 < primeScale d p :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp) _

lemma primeScale_pow {d p : ℕ} (hd : 0 < d) : (primeScale d p)^d = p := by
  rw [primeScale,←Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ p),
    inv_mul_cancel₀ (by exact_mod_cast hd.ne' : (d:ℝ) ≠ 0),Real.rpow_one]

lemma primeScale_pow_mul {d p r : ℕ} (hd : 0 < d) : (primeScale d p)^(r*d) = (p:ℝ)^r := by
  rw [Nat.mul_comm r d,pow_mul,primeScale_pow hd]


lemma prime_grid_density {d : ℕ} (hd : 0 < d) {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (hconv : Convex ℝ J) (h0 : 0 ∈ J) :
    Tendsto (fun p : ℕ => ((integerGrid J hJ (primeScale d p)).card:ℝ)/(p:ℝ)) atTop
      (𝓝 (volume.real J)) := by
  simpa only [Function.comp_def,primeScale_pow hd] using
    (normalized_card_limit hJ hconv h0).comp (primeScale_tendsto hd)



lemma eventually_prime_grid_bound {d k : ℕ} (hk : k < d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    ∀ᶠ p : ℕ in atTop, ∃ B : ℕ, 1 ≤ B ∧
      (∀ z ∈ integerGrid J hJ (primeScale d p), ∀ j, |z j| ≤ (B:ℤ)) ∧
      k.factorial*B^k < p := by
  obtain ⟨C,hC,hbound⟩ := grid_uniform_bound hJ
  have h2C : 1 ≤ 2*C := by linarith
  filter_upwards [eventually_subcritical_minor_bound hk h2C,
    (primeScale_tendsto (by omega : 0 < d)).eventually (eventually_ge_atTop (1:ℝ))]
    with p hp ht
  let B : ℕ := ⌈C*primeScale d p⌉₊
  have hCt : 1 ≤ C*primeScale d p := one_le_mul_of_one_le_of_one_le hC ht
  have hB : (1:ℝ) ≤ B := hCt.trans (Nat.le_ceil _)
  have hBC : (B:ℝ) ≤ 2*C*primeScale d p := by
    have hh := (Nat.ceil_lt_add_one (by linarith : 0 ≤ C*primeScale d p)).le
    dsimp only [B]
    nlinarith
  refine ⟨B,by exact_mod_cast hB,?_,?_⟩
  · intro z hz j
    have hh := (hbound _ ht z hz j).trans (Nat.le_ceil _)
    exact_mod_cast hh
  · have hh : (k.factorial:ℝ)*(B:ℝ)^k < (p:ℝ) :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg B) hBC k)
        (Nat.cast_nonneg _)).trans_lt hp.2
    exact_mod_cast hh



theorem eventually_prime_circuit_count_le {d r : ℕ} (hr : 0 < r) (hd : 2*(r+1) ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J) (h0 : 0 ∈ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      ((circuits (integerGrid J hJ (primeScale d p)) r).card:ℝ)/(p:ℝ)^r <
        (SimplexYoung.affineCircuitVolumeSum (r:=r) J).toReal+ε := by
  obtain ⟨B,hB,hbound⟩ := grid_uniform_bound hJ
  have hh := eventually_circuit_count_le hr hd hJ hconv h0 (integerGrid J hJ) hB hbound
    (fun t ht z hz => (mem_integerGrid hJ (by linarith : t ≠ 0)).mp hz) hε
  simpa only [primeScale_pow_mul (by omega : 0 < d)] using
    (primeScale_tendsto (by omega : 0 < d)).eventually hh




end SingleLatticeCovering.ConvexGrid


noncomputable section
namespace SingleLatticeCovering.GridProbability
open Filter Topology
open scoped BigOperators

lemma cardinality_tendsto_atTop {M : ℕ → ℕ} {V : ℝ} (hV : 0 < V)
    (hM : Tendsto (fun p => (M p:ℝ)/(p:ℝ)) atTop (𝓝 V)) :
    Tendsto (fun p => (M p:ℝ)) atTop atTop := by
  have hh := hM.pos_mul_atTop hV (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  exact div_mul_cancel₀ _ (by exact_mod_cast (show p ≠ 0 by omega))



lemma normalized_choose_tendsto {M : ℕ → ℕ} {V : ℝ} (hV : 0 < V)
    (hM : Tendsto (fun p => (M p:ℝ)/(p:ℝ)) atTop (𝓝 V)) (j : ℕ) :
    Tendsto (fun p => ((M p).choose j:ℝ)/(p:ℝ)^j) atTop
      (𝓝 (V^j/(j.factorial:ℝ))) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hinv : Tendsto (fun p : ℕ => (j:ℝ)/(p:ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero,div_eq_mul_inv,Pi.inv_apply] using
        (tendsto_natCast_atTop_atTop (R:=ℝ)).inv_tendsto_atTop.const_mul (j:ℝ)
    have ht := (ih.mul (hM.sub hinv)).div_const (j+1:ℝ)
    have hlim : (V^j/(j.factorial:ℝ))*(V-0)/(j+1:ℝ) = V^(j+1)/((j+1).factorial:ℝ) := by
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ,sub_zero]
      field_simp
    rw [hlim] at ht
    apply ht.congr'
    filter_upwards [(cardinality_tendsto_atTop hV hM).eventually (eventually_ge_atTop (j:ℝ)),
      eventually_ge_atTop 1] with p hpj hp1
    have hjM : j ≤ M p := by exact_mod_cast hpj
    have hc :
        (((M p).choose (j+1):ℕ):ℝ)*(j+1:ℝ) =
          (((M p).choose j:ℕ):ℝ)*((M p:ℝ)-(j:ℝ)) := by
      exact_mod_cast Nat.choose_succ_right_eq (M p) j
    have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hj0 : (j+1:ℝ) ≠ 0 := by positivity
    field_simp [hp0,hj0,pow_succ]
    rw [←hc,pow_succ]
    ring

lemma binomial_polynomial_limit {M : ℕ → ℕ} {V : ℝ} (hV : 0 < V)
    (hM : Tendsto (fun p => (M p:ℝ)/(p:ℝ)) atTop (𝓝 V)) (k : ℕ) :
    Tendsto (fun p => ∑ j ∈ Finset.range (k+1), ((M p).choose j:ℝ)*(-1:ℝ)^j*((p:ℝ)⁻¹)^j)
      atTop (𝓝 (∑ j ∈ Finset.range (k+1), (-1:ℝ)^j*V^j/(j.factorial:ℝ))) := by
  have hh := tendsto_finsetSum (Finset.range (k+1))
    (fun j hj => (normalized_choose_tendsto hV hM j).const_mul ((-1:ℝ)^j))
  simpa only [inv_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh

lemma binomial_envelope_le_exp (M p : ℕ) :
    (1+(p:ℝ)⁻¹)^M ≤ Real.exp ((M:ℝ)/(p:ℝ)) := by
  calc
    _ ≤ (Real.exp ((p:ℝ)⁻¹))^M :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((p:ℝ)⁻¹)]) M
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1



lemma upper_envelope_limit {α : Type*} {l : Filter α} {f : α → ℝ} {C : ℝ}
    (hf : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, f x < C+ε) :
    Tendsto (fun x => max (f x) C) l (𝓝 C) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall (fun x => hb.trans_le (le_max_right _ _))
  · intro b hb
    filter_upwards [hf (b-C) (sub_pos.mpr hb)] with x hx
    exact max_lt (by linarith) hb




end SingleLatticeCovering.GridProbability

namespace SingleLatticeCovering.ConvexGrid
open MeasureTheory Filter Topology AffineCircuit GridProbability BrokenCircuit PrimeCircuit
open scoped BigOperators


def primeGridVoid {d : ℕ} (J : Set (Fin d → ℝ)) (hJ : IsCompact J)
    (p : ℕ) [Fact p.Prime] : ℝ :=
  vectorAverage (fun a : Fin (d+1) → ZMod p => avoidanceIndicator
    (fun z : integerGrid J hJ (primeScale d p) => homogeneousRow (p:=p) z.val)
    (dotProductBilin (ZMod p) (ZMod p) a))

def continuumCircuitError {d : ℕ} (J : Set (Fin d → ℝ)) (k : ℕ) : ℝ :=
  Real.exp (volume.real J) * ∑ r ∈ Finset.Icc 2 k,
    (SimplexYoung.affineCircuitVolumeSum (r:=r) J).toReal/(r.factorial:ℝ)



theorem eventually_primeGridVoid_le {d q : ℕ} (hq : 0 < q)
    (hd : 2*(2*q+1) ≤ d) {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (hconv : Convex ℝ J) (h0 : 0 ∈ J)
    (hV : 0 < volume.real J) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      primeGridVoid J hJ p ≤
        (∑ j ∈ Finset.range (2*q+1), (-1:ℝ)^j*(volume.real J)^j/(j.factorial:ℝ)) +
          continuumCircuitError J (2*q)+ε := by
  classical
  let S (p : ℕ) := integerGrid J hJ (primeScale d p)
  let C (r : ℕ) := (SimplexYoung.affineCircuitVolumeSum (r:=r) J).toReal
  let U (p r : ℕ) := max (((circuits (S p) r).card:ℝ)/(p:ℝ)^r) (C r)
  have hU (r : ℕ) (hr : r ∈ Finset.Icc 2 (2*q)) :
      Tendsto (fun p => U p r) atTop (𝓝 (C r)) := by
    apply upper_envelope_limit
    intro δ hδ
    exact eventually_prime_circuit_count_le (by have := (Finset.mem_Icc.mp hr).1; omega)
      (by have := (Finset.mem_Icc.mp hr).2; omega) hJ hconv h0 hδ
  have hsum := tendsto_finsetSum (Finset.Icc 2 (2*q))
    (fun r hr => (hU r hr).div_const (r.factorial:ℝ))
  have hmass := prime_grid_density (by omega : 0 < d) hJ hconv h0
  have hlim := (binomial_polynomial_limit hV hmass (2*q)).add (((Real.continuous_exp.tendsto _).comp hmass).mul hsum)
  have hless :
      (∑ j ∈ Finset.range (2*q+1), (-1:ℝ)^j*(volume.real J)^j/(j.factorial:ℝ)) +
        Real.exp (volume.real J) * ∑ r ∈ Finset.Icc 2 (2*q), C r/(r.factorial:ℝ) <
      (∑ j ∈ Finset.range (2*q+1), (-1:ℝ)^j*(volume.real J)^j/(j.factorial:ℝ)) +
        continuumCircuitError J (2*q)+ε := by
    change _ + continuumCircuitError J (2*q) < _
    exact lt_add_of_pos_right _ hε
  have hevent := hlim.eventually (gt_mem_nhds hless)
  have hminor := eventually_prime_grid_bound (k:=2*q+1) (by omega) hJ
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hevent.and hminor)
  refine ⟨N,?_⟩
  intro p hpPrime hpN
  obtain ⟨he,⟨B,hB,hSB,hpB⟩⟩ := hN p hpN
  let : LinearOrder (S p) := (Fintype.equivFin (S p)).linearOrder
  have hp2 : 2*B < p := by
    have hf : 2 ≤ (2*q+1).factorial := by
      simpa using (Nat.factorial_le (show 2 ≤ 2*q+1 by omega))
    have hb : B ≤ B^(2*q+1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1 ≤ 2*q+1 by omega)
    exact (Nat.mul_le_mul hf hb).trans_lt hpB
  let v : S p → Fin (d+1) → ZMod p := fun z => homogeneousRow z.val
  have hfin := finite_field_void_upper v q
  simp only [ZMod.card,Fintype.card_coe] at hfin
  have herr := finiteCircuitError_le (k:=2*q) (S p) hB hSB hp2 hpB
  have hsn : 0 ≤ ∑ r ∈ Finset.Icc 2 (2*q),
      ((circuits (S p) r).card:ℝ)/(p:ℝ)^r/(r.factorial:ℝ) := by
    apply Finset.sum_nonneg
    intro r hr
    exact div_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)
  have hreplace : ∑ r ∈ Finset.Icc 2 (2*q),
      ((circuits (S p) r).card:ℝ)/(p:ℝ)^r/(r.factorial:ℝ) ≤
        ∑ r ∈ Finset.Icc 2 (2*q), U p r/(r.factorial:ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    exact div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
  have herr' := herr.trans ((mul_le_mul_of_nonneg_right (binomial_envelope_le_exp (S p).card p) hsn).trans
    (mul_le_mul_of_nonneg_left hreplace (Real.exp_pos _).le))
  exact (hfin.trans (add_le_add le_rfl herr')).trans he.le


end SingleLatticeCovering.ConvexGrid

namespace SingleLatticeCovering.SimplexYoung
open scoped BigOperators
lemma simplexConstant_sq_ratio {r : ℕ} (hr : 0 < r) :
    (simplexConstant r)^2 = ((r+1:ℕ):ℝ)^r / ((r:ℝ)^r * (r+1:ℕ)) := by
  have h : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  unfold simplexConstant
  rw [div_pow, ←pow_mul, mul_comm r 2, pow_mul, inv_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), inv_div, div_pow]
  ring

lemma simplexConstant_succ_sq {r : ℕ} (hr : 0 < r) :
    (simplexConstant (r+1))^2 = (simplexConstant r)^2 *
      (1 - 1 / (((r+1:ℕ):ℝ)^2))^r := by
  have h : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have h1 : ((r+1:ℕ):ℝ) ≠ 0 := by positivity
  have h2 : ((r+1+1:ℕ):ℝ) ≠ 0 := by positivity
  rw [simplexConstant_sq_ratio (by omega), simplexConstant_sq_ratio hr]
  have hc : (1 - 1 / (((r+1:ℕ):ℝ)^2)) = (r:ℝ) * (r+2) / (((r+1:ℕ):ℝ)^2) := by
    push_cast
    field_simp
    ring
  rw [hc, div_pow, mul_pow, pow_succ, pow_succ, ←pow_mul]
  push_cast
  rw [show 2*r=r+r by omega, pow_add]
  field_simp
  ring

lemma simplexConstant_succ_le {r : ℕ} (hr : 0 < r) :
    simplexConstant (r+1) ≤ simplexConstant r * Real.exp (-(r:ℝ)/(2*((r+1:ℕ):ℝ)^2)) := by
  have hbase : 0 ≤ 1 - 1 / (((r+1:ℕ):ℝ)^2) := by
    have h : (1:ℝ) ≤ (r+1:ℕ) := by exact_mod_cast (show 1 ≤ r+1 by omega)
    have hsq : (1:ℝ) ≤ ((r+1:ℕ):ℝ)^2 := by nlinarith
    have hi := (div_le_one (by positivity : (0:ℝ)<((r+1:ℕ):ℝ)^2)).mpr hsq
    linarith
  have hexp : (1 - 1 / (((r+1:ℕ):ℝ)^2))^r ≤ Real.exp (-(r:ℝ)/((r+1:ℕ):ℝ)^2) := by
    calc
      _ ≤ (Real.exp (-(1 / (((r+1:ℕ):ℝ)^2))))^r :=
        pow_le_pow_left₀ hbase (by linarith [Real.add_one_le_exp (-(1/(((r+1:ℕ):ℝ)^2)))]) r
      _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring
  apply (sq_le_sq₀ (simplexConstant_nonneg _) (mul_nonneg (simplexConstant_nonneg _) (Real.exp_pos _).le)).mp
  rw [simplexConstant_succ_sq hr, mul_pow, ←Real.exp_nat_mul]
  have he : (2:ℝ) * (-(r:ℝ)/(2*((r+1:ℕ):ℝ)^2)) = -(r:ℝ)/((r+1:ℕ):ℝ)^2 := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  exact mul_le_mul_of_nonneg_left hexp (sq_nonneg _)



def circuitTerm (d : ℕ) (V : ℝ) (r : ℕ) : ℝ :=
  (4:ℝ)^r * (simplexConstant r)^d * V^r / (r.factorial:ℝ)

lemma circuitTerm_nonneg (d r : ℕ) {V : ℝ} (hV : 0 ≤ V) :
    0 ≤ circuitTerm d V r := by
  unfold circuitTerm
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (pow_nonneg (simplexConstant_nonneg _) _)) (pow_nonneg hV _)) (by positivity)

lemma circuitTerm_succ_le {d r : ℕ} (hr : 3 ≤ r) {V : ℝ}
    (hV : 0 ≤ V) (hVd : V ≤ (d:ℝ)/6) :
    circuitTerm d V (r+1) ≤ (3/4:ℝ) * circuitTerm d V r := by
  have hr0 : 0 < r := by omega
  have hden : (0:ℝ) < (r+1:ℕ) := by positivity
  have hgeo := pow_le_pow_left₀ (simplexConstant_nonneg _) (simplexConstant_succ_le hr0) d
  rw [mul_pow, ←Real.exp_nat_mul] at hgeo
  have hexp : -(d:ℝ) * (r:ℝ)/(2*((r+1:ℕ):ℝ)^2) ≤
      -(3:ℝ)/8 * ((d:ℝ)/(r+1:ℕ)) := by
    have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*((r+1:ℕ):ℝ)^2)).mpr
    have he : (-(3:ℝ)/8 * ((d:ℝ)/(r+1:ℕ))) * (2*((r+1:ℕ):ℝ)^2) =
        -(3:ℝ)/4 * (d:ℝ) * ((r+1:ℕ):ℝ) := by field_simp; ring
    rw [he]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0:ℝ)≤d) (sub_nonneg.mpr hrR)]
  have heq : (d:ℝ) * (-(r:ℝ)/(2*((r+1:ℕ):ℝ)^2)) =
      -(d:ℝ) * (r:ℝ)/(2*((r+1:ℕ):ℝ)^2) := by ring
  rw [heq] at hgeo
  have hgeo' := hgeo.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexp) (pow_nonneg (simplexConstant_nonneg _) _))
  have hb : (4*V/(r+1:ℕ))*Real.exp (-(3:ℝ)/8*((d:ℝ)/(r+1:ℕ))) ≤ 3/4 := by
    have ht := Real.mul_exp_neg_le_exp_neg_one ((3:ℝ)/8*((d:ℝ)/(r+1:ℕ)))
    have he : Real.exp (-1) ≤ (27/64:ℝ) := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      nlinarith [Real.exp_one_gt_d9]
    calc
      _ ≤ ((2:ℝ)/3*((d:ℝ)/(r+1:ℕ)))*Real.exp (-(3:ℝ)/8*((d:ℝ)/(r+1:ℕ))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply (div_le_iff₀ hden).mpr
        have heq : ((2:ℝ)/3*((d:ℝ)/(r+1:ℕ)))*((r+1:ℕ):ℝ) = (2:ℝ)/3*d := by field_simp
        rw [heq]
        linarith
      _ = (16/9:ℝ)*(((3:ℝ)/8*((d:ℝ)/(r+1:ℕ)))*
          Real.exp (-((3:ℝ)/8*((d:ℝ)/(r+1:ℕ))))) := by
        rw [show -(3:ℝ)/8*((d:ℝ)/(r+1:ℕ)) = -((3:ℝ)/8*((d:ℝ)/(r+1:ℕ))) by ring]
        ring
      _ ≤ (16/9:ℝ)*Real.exp (-1) := mul_le_mul_of_nonneg_left ht (by norm_num)
      _ ≤ 3/4 := by linarith
  unfold circuitTerm
  rw [pow_succ, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ((4:ℝ)^r*4) * ((simplexConstant r)^d *
        Real.exp (-(3:ℝ)/8*((d:ℝ)/(r+1:ℕ)))) * (V^r*V) /
        (((r:ℝ)+1)*(r.factorial:ℝ)) := by gcongr
    _ = ((4*V/(r+1:ℕ))*Real.exp (-(3:ℝ)/8*((d:ℝ)/(r+1:ℕ)))) *
        ((4:ℝ)^r*(simplexConstant r)^d*V^r/(r.factorial:ℝ)) := by push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (circuitTerm_nonneg d r hV)


lemma circuitTerm_add_three_le {d : ℕ} {V : ℝ} (hV : 0 ≤ V)
    (hVd : V ≤ (d:ℝ)/6) (s : ℕ) :
    circuitTerm d V (s+3) ≤ (3/4:ℝ)^s * circuitTerm d V 3 := by
  induction s with
  | zero => simp
  | succ s ih =>
    calc
      _ ≤ (3/4:ℝ) * circuitTerm d V (s+3) := circuitTerm_succ_le (by omega) hV hVd
      _ ≤ (3/4:ℝ) * ((3/4:ℝ)^s * circuitTerm d V 3) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring



theorem tsum_circuitTerm_le {d : ℕ} {V : ℝ} (hV : 0 ≤ V)
    (hVd : V ≤ (d:ℝ)/6) :
    ∑' s : ℕ, ENNReal.ofReal (circuitTerm d V (s+3)) ≤
      ENNReal.ofReal (4 * circuitTerm d V 3) := by
  calc
    _ ≤ ∑' s : ℕ, ENNReal.ofReal ((3/4:ℝ)^s * circuitTerm d V 3) :=
      ENNReal.tsum_le_tsum (fun s => ENNReal.ofReal_le_ofReal (circuitTerm_add_three_le hV hVd s))
    _ = ENNReal.ofReal (4 * circuitTerm d V 3) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun s => mul_nonneg (by positivity)
        (circuitTerm_nonneg _ _ hV))
        ((summable_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖ < 1)).mul_right _)]
      rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖ < 1)]
      norm_num




end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
lemma sharpParallelogramConstant_pos : 0 < (4 * (Real.sqrt 3)⁻¹^3 : ℝ) := by positivity

lemma sharpParallelogramConstant_sq : (4 * (Real.sqrt 3)⁻¹^3 : ℝ)^2 = 16/27 := by
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  calc
    _ = 16 / (Real.sqrt 3)^6 := by field_simp; ring
    _ = _ := by rw [show 6 = 2*3 from rfl, pow_mul, hs]; norm_num

lemma sharpParallelogramConstant_exp (d : ℕ) :
    (4 * (Real.sqrt 3)⁻¹^3 : ℝ)^d =
      Real.exp (-(d:ℝ)/2 * Real.log (27/16:ℝ)) := by
  have hp := sharpParallelogramConstant_pos
  have hlog := congrArg Real.log sharpParallelogramConstant_sq
  rw [Real.log_pow] at hlog
  have hi : Real.log (16/27:ℝ) = -Real.log (27/16:ℝ) := by
    rw [← Real.log_inv]; norm_num
  rw [hi] at hlog
  rw [← Real.exp_log hp, ← Real.exp_nat_mul]
  congr 1
  push_cast at hlog
  nlinarith


def sourceEta (d : ℕ) : ℝ := (d:ℝ)/4 * Real.log (27/16:ℝ) - 3*Real.log (d:ℝ)

lemma sourceLog_pos : 0 < Real.log (27/16:ℝ) := Real.log_pos (by norm_num)

lemma sourceLog_le_one : Real.log (27/16:ℝ) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<27/16)
  linarith

lemma sourceEta_le_dim {d : ℕ} (hd : 1 ≤ d) : sourceEta d ≤ d := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hl : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg hdR
  have hx := sourceLog_le_one
  dsimp [sourceEta]
  nlinarith


lemma log_27_16_le : Real.log (27/16 : ℝ)≤8/15 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ)<27/16)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤8/15) 4
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith

lemma sourceEta_le_linear (d : ℕ) : sourceEta d≤(2/15 : ℝ)*d := by
  have h := mul_le_mul_of_nonneg_left log_27_16_le (show (0 : ℝ)≤(d : ℝ)/4 by positivity)
  have hlog := Real.log_natCast_nonneg d
  unfold sourceEta
  nlinarith


lemma simplexConstant_three : simplexConstant 3 = 4 * (Real.sqrt 3)⁻¹^3 := by
  unfold simplexConstant
  norm_num [Real.sqrt_div, div_pow]
  ring

lemma circuitTerm_three_source {d : ℕ} (hd : 1 ≤ d) {V : ℝ}
    (hV : 0 ≤ V) (hVeta : V ≤ sourceEta d) :
    Real.exp V * (4 * circuitTerm d V 3) ≤ (128/3:ℝ) * Real.exp (-sourceEta d) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hVd := hVeta.trans (sourceEta_le_dim hd)
  have hpow : V^3 ≤ (d:ℝ)^3 := pow_le_pow_left₀ hV hVd _
  have h : Real.exp V * ((4*(Real.sqrt 3)⁻¹^3:ℝ)^d * V^3) ≤ Real.exp (-sourceEta d) := by
    rw [sharpParallelogramConstant_exp]
    calc
      _ ≤ Real.exp V * (Real.exp (-(d:ℝ)/2*Real.log (27/16:ℝ)) * (d:ℝ)^3) := by gcongr
      _ = Real.exp (V-(d:ℝ)/2*Real.log (27/16:ℝ)+3*Real.log (d:ℝ)) := by
        have he : (d:ℝ)^3 = Real.exp (3*Real.log (d:ℝ)) := by
          simpa only [Nat.cast_ofNat, Real.exp_log hdR] using (Real.exp_nat_mul (Real.log (d:ℝ)) 3).symm
        rw [he, ←Real.exp_add, ←Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hl := Real.log_nonneg (show (1:ℝ)≤d by exact_mod_cast hd)
        dsimp [sourceEta] at hVeta ⊢
        linarith
  unfold circuitTerm
  rw [simplexConstant_three]
  norm_num only [show (4:ℝ)^3=64 by norm_num, show ((3:ℕ).factorial:ℝ)=6 by norm_num]
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤128/3)
  calc
    _ = (128/3:ℝ) * (Real.exp V * ((4*(Real.sqrt 3)⁻¹^3:ℝ)^d * V^3)) := by ring
    _ ≤ _ := hh




theorem circuit_series_at_sourceEta {d : ℕ} (hd : 1 ≤ d) {V : ℝ}
    (hV : 0 ≤ V) (hVeta : V ≤ sourceEta d) :
    ENNReal.ofReal (Real.exp V) *
      (∑' s : ℕ, ENNReal.ofReal (circuitTerm d V (s+3))) ≤
        ENNReal.ofReal ((128/3:ℝ)*Real.exp (-sourceEta d)) := by
  have hVd : V ≤ (d:ℝ)/6 := by
    have h := hVeta.trans (sourceEta_le_linear d)
    nlinarith [(Nat.cast_nonneg d : (0:ℝ)≤d)]
  calc
    _ ≤ ENNReal.ofReal (Real.exp V) * ENNReal.ofReal (4*circuitTerm d V 3) :=
      mul_le_mul_right (tsum_circuitTerm_le hV hVd) _
    _ = ENNReal.ofReal (Real.exp V * (4*circuitTerm d V 3)) :=
      (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (circuitTerm_three_source hd hV hVeta)


end SingleLatticeCovering.SimplexYoung




noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Finset Set
open scoped BigOperators

def poissonPartial (u : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k+1), (-u)^j/(j.factorial : ℝ)

lemma poissonPartial_zero (k : ℕ) : poissonPartial 0 k=1 := by
  unfold poissonPartial
  rw [sum_range_succ']
  simp

lemma taylor_exp_neg_eq {u : ℝ} (hu : 0 < u) (k : ℕ) :
    taylorWithinEval Real.exp k (uIcc 0 (-u)) 0 (-u)=poissonPartial u k := by
  have hne : (0 : ℝ)≠-u := by linarith
  have hd (j : ℕ) : iteratedDerivWithin j Real.exp (uIcc 0 (-u)) 0=1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      Real.contDiff_exp.contDiffAt (left_mem_uIcc),iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp,Real.exp_zero]
  rw [taylor_within_apply]
  unfold poissonPartial
  apply Finset.sum_congr rfl
  intro j hj
  rw [hd]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]


theorem poissonPartial_error {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    |poissonPartial u k-Real.exp (-u)| ≤ u^(k+1)/(k+1).factorial := by
  rcases hu.eq_or_lt with he | hu
  · subst u
    simp [poissonPartial_zero]
  have hne : (0 : ℝ)≠-u := by linarith
  obtain ⟨c,hc,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := k) hne
    Real.contDiff_exp.contDiffOn
  rw [taylor_exp_neg_eq hu k,iteratedDeriv_eq_iterate,Real.iter_deriv_exp,sub_zero] at he
  have hc0 : c ≤ 0 := by
    have h := hc.2
    simpa only [max_eq_left (neg_nonpos.mpr hu.le)] using h.le
  have hec : Real.exp c ≤ 1 := by simpa using Real.exp_le_exp.mpr hc0
  rw [abs_sub_comm,he,abs_div,abs_mul,abs_pow,abs_neg,abs_of_nonneg hu.le,
    abs_of_pos (Real.exp_pos c),abs_of_nonneg (by positivity : (0 : ℝ)≤(k+1).factorial)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_of_le_one_left (by positivity) hec



theorem poissonPartial_upper {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    poissonPartial u k ≤ Real.exp (-u)+u^(k+1)/(k+1).factorial := by
  have := le_trans (le_abs_self (poissonPartial u k-Real.exp (-u)))
    (poissonPartial_error hu k)
  linarith


end SingleLatticeCovering.RogersPreparation

namespace SingleLatticeCovering.SimplexYoung
open scoped BigOperators
lemma log_four_thirds_ge : (2/7 : ℝ)≤Real.log (4/3 : ℝ) := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ)<4/3)).mpr
  have h := Real.exp_le_two_add_div_two_sub (by norm_num : (0 : ℝ)≤2/7)
    (by norm_num : (2/7 : ℝ)<2)
  norm_num at h ⊢
  exact h

lemma log_three_quarters_le : Real.log (3/4 : ℝ)≤-(2/7 : ℝ) := by
  have he : (3/4 : ℝ)=(4/3 : ℝ)⁻¹ := by norm_num
  rw [he,Real.log_inv]
  linarith [log_four_thirds_ge]

lemma factorial_quotient_chernoff {u : ℝ} (hu : 0≤u) {q : ℕ} (hq : 0<q) :
    u^q/(q.factorial : ℝ)≤(Real.exp 1*u/(q : ℝ))^q := by
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have h := Real.pow_div_factorial_le_exp (q : ℝ) (Nat.cast_nonneg q : (0 : ℝ)≤q) q
  calc
    _ = (u/(q : ℝ))^q*((q : ℝ)^q/(q.factorial : ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ (u/(q : ℝ))^q*Real.exp (q : ℝ) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg (div_nonneg hu hqR.le) _)
    _ = _ := by
      have he : Real.exp (q : ℝ) = Real.exp 1 ^ q := by
        simp
      rw [he, div_pow, div_pow, mul_pow]
      ring



theorem poisson_remainder_circuitCutoff {d : ℕ} (hd : 270≤d) {u : ℝ}
    (hu : 0≤u) (huη : u ≤ sourceEta d) :
    u^(2*(d/4-1)+1)/((2*(d/4-1)+1).factorial : ℝ)≤Real.exp (-sourceEta d) := by
  let q := 2*(d/4-1)+1
  have hq : 0<q := by dsimp [q]; omega
  have hdR : (270 : ℝ)≤d := by exact_mod_cast hd
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hqlo : (d : ℝ)/2-3≤q := by
    have hfloor : d≤4*(d/4)+3 := by omega
    have hcast : (d : ℝ)≤4*(d/4 : ℕ)+3 := by exact_mod_cast hfloor
    have hf : 1 ≤ d/4 := by omega
    simp only [q,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hf,Nat.cast_one]
    linarith
  have hqratio : (22/45 : ℝ)*d≤q := by linarith
  have hqexponent : (7/15 : ℝ)*d≤q := by linarith
  have hue : u≤(2/15 : ℝ)*d := huη.trans (sourceEta_le_linear d)
  have he : Real.exp 1≤(11/4 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hratio : Real.exp 1*u/(q : ℝ)≤(3/4 : ℝ) := by
    apply (div_le_iff₀ hqR).mpr
    have hc := mul_le_mul_of_nonneg_right he hu
    nlinarith
  have hlog : (q : ℝ)*Real.log (3/4 : ℝ)≤-(2/15 : ℝ)*d := by
    have h := mul_le_mul_of_nonneg_left log_three_quarters_le hqR.le
    linarith
  change u^q/(q.factorial : ℝ)≤_
  calc
    _ ≤ (Real.exp 1*u/(q : ℝ))^q := factorial_quotient_chernoff hu hq
    _ ≤ (3/4 : ℝ)^q := pow_le_pow_left₀ (by positivity) hratio q
    _ = Real.exp ((q : ℝ)*Real.log (3/4 : ℝ)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<3/4)]
    _ ≤ Real.exp (-(2/15 : ℝ)*d) := Real.exp_le_exp.mpr hlog
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [sourceEta_le_linear d])


end SingleLatticeCovering.SimplexYoung


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
