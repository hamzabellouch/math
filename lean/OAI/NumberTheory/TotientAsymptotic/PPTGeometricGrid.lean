import OAI.NumberTheory.TotientAsymptotic.PPTPointwiseGrid

namespace OAI

/-! Prime-coordinate contraction supplies the two geometric hypotheses
of the actual residual-grid theorem, including its singleton case. -/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma ppt_terminal_first_cutoff_loss {γ : ℝ} (_hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, ∀ L U : ℝ,
      L ≤ U → U ≤ 2*t^(2/3 : ℝ) →
      (L+U)/(2*t) ≤ 1-γ/(Real.log t)^3 := by
  filter_upwards [(tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*γ))),
    eventually_gt_atTop (0 : ℝ)] with t hsmall hlog ht
  intro L U hLU hU
  have hlog1 : 1 ≤ Real.log t := (le_max_left _ _).trans hlog
  have hlogγ : 2*γ ≤ Real.log t := (le_max_right _ _).trans hlog
  have hlog0 : 0 < Real.log t := zero_lt_one.trans_le hlog1
  have hp : Real.log t ≤ (Real.log t)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hlog1 (show 1 ≤ 3 by omega)
  have hγsmall : γ/(Real.log t)^3 ≤ 1/2 := by
    apply (div_le_iff₀ (pow_pos hlog0 3)).mpr
    linarith only [hlogγ,hp]
  have he : t^(2/3 : ℝ)/t = t^(-(1/3 : ℝ)) := by
    calc
      _ = t^(2/3 : ℝ)/t^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub ht]; norm_num
  have hbound : (L+U)/(2*t) ≤ 2*(t^(2/3 : ℝ)/t) := by
    apply (div_le_iff₀ (show 0 < 2*t by positivity)).mpr
    have heq : (2*(t^(2/3 : ℝ)/t))*(2*t) = 4*t^(2/3 : ℝ) := by field_simp; norm_num
    rw [heq]
    linarith only [hLU,hU]
  rw [he] at hbound
  linarith only [hbound,hsmall,hγsmall]

/-- Passing to an ordered sublist retains one common inverse-cube
contraction, measured by the remaining length at its first coordinate. -/
lemma ppt_geometric_embedded_contraction {m n b H : ℕ} {budget c : ℝ}
    {v : Fin n → ℝ} (hv : v ∈ relaxedGeometricFamily m n budget c)
    (hnm : n ≤ m) (ι : Fin b ↪o Fin n) (hb : 0 < b)
    (hH : m-(ι ⟨0,hb⟩).val ≤ H) :
    1/(10*(H : ℝ)^3) ≤ 1 ∧
      ∀ i j : Fin b, i < j →
        v (ι j) ≤ v (ι i)/(1+1/(10*(H : ℝ)^3)) := by
  have hrem (i : Fin b) : 1 ≤ m-(ι i).val := by
    have hi := (ι i).isLt
    omega
  have hremH (i : Fin b) : m-(ι i).val ≤ H := by
    have hi := ι.monotone (show (⟨0,hb⟩ : Fin b) ≤ i from Nat.zero_le _)
    change (ι ⟨0,hb⟩).val ≤ (ι i).val at hi
    omega
  have hHpos : 1 ≤ H := (hrem ⟨0,hb⟩).trans (hremH ⟨0,hb⟩)
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hHpos
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHr
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 10*(H : ℝ)^3)).mpr
    have hh : (1 : ℝ) ≤ (H : ℝ)^3 := one_le_pow₀ hHr
    linarith only [hh]
  · intro i j hij
    have hactual := hv.2.2 (ι i) (ι j) (ι.strictMono hij)
    have hidentity : rowContractionError (m-((ι i).val+1))/2 =
        1/(10*((m-(ι i).val : ℕ) : ℝ)^3) := by
      have he : m-((ι i).val+1)+1 = m-(ι i).val := by
        have hi := (ι i).isLt
        omega
      have her : ((m-((ι i).val+1) : ℕ) : ℝ)+1 = ((m-(ι i).val : ℕ) : ℝ) := by
        exact_mod_cast he
      dsimp only [rowContractionError]
      rw [her]
      ring
    rw [hidentity] at hactual
    apply hactual.trans
    have hrem0 : (0 : ℝ) < (m-(ι i).val : ℕ) := by
      exact_mod_cast (zero_lt_one.trans_le (hrem i))
    have hp := pow_le_pow_left₀ hrem0.le (Nat.cast_le.mpr (hremH i)) 3
    have hrec : 1/(10*(H : ℝ)^3) ≤ 1/(10*((m-(ι i).val : ℕ) : ℝ)^3) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left hp (by norm_num))
    exact div_le_div_of_nonneg_left (hv.1.1 (ι i)) (by positivity)
      (by linarith only [hrec])

/-- An actual prime row gives both the first-cutoff loss and all paired
grid gaps.  No coordinate separation is assumed after taking largest
factors: those errors are supplied by normality and the doubled mesh. -/
theorem ppt_geometric_pair_grid {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (b H : ℕ) (S L U ω : ℝ) (p : ShiftedPair b), ∀ _hb : 0 < b,
      b ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      1 < S → 0 ≤ B S → S ≤ z →
      (∀ i, IsNormalPrime S (p.left i)) →
      (∀ i, 3 ≤ p.left i) →
      (∀ i, (p.left i-1 : ℕ) ≤ z) →
      1/(10*(H : ℝ)^3) ≤ ω → ω ≤ 1 →
      (∀ i : Fin b, (B z)^(2/3 : ℝ) ≤ B (p.left i)) →
      (∀ i : Fin b, ∀ hi : i.val+1 < b,
        B (p.left ⟨i.val+1,hi⟩) ≤ B (p.left i)/(1+ω)) →
      L ≤ U → U ≤ 2*(B z)^(2/3 : ℝ) →
      let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
      let u := fun i => B (largestPrimeFactor (p.left i-1))/B z
      let v := fun i => B (largestPrimeFactor (p.right i-1))/B z
      (∀ i, |u i-v i| ≤ (2*(i.val : ℝ)+1)*δ) →
      let label := fun i => collisionGridIndex δ (u i) (v i)
      pairedGridUpper δ ((L+U)/(2*B z)) label 1 ≤ 
        1-(1/(80*A^3))/(Real.log (B z))^3 ∧
      (∀ i : Fin b, ∀ hi : i.val+1 < b,
        max (u ⟨i.val+1,hi⟩) (v ⟨i.val+1,hi⟩)+
          (2*(i.val : ℝ)+8)*δ < min (u i) (v i)) := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [ppt_normal_factor_loss_mesh,
    B_tendsto.eventually (ppt_local_contracted_grid_separation hA),
    B_tendsto.eventually (ppt_local_contracted_first_loss hA),
    B_tendsto.eventually (ppt_terminal_first_cutoff_loss hγ),
    B_tendsto.eventually (ppt_log_dimension_separation hA),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_ge_atTop (Real.exp 1)] with z hfactor hgap hfirst hterminal hseparation hB hz
  intro b H S L U ω p hb hbH hdim hS hBS hSz hp hp3 hpz hω hω1 hlarge
    hcontract hLU hU
  dsimp only
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  let u := fun i => B (largestPrimeFactor (p.left i-1))/B z
  let v := fun i => B (largestPrimeFactor (p.right i-1))/B z
  intro halign
  let label := fun i => collisionGridIndex δ (u i) (v i)
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hH : 1 ≤ H := by omega
  have hδ : 0 < δ := by
    have hlog : 0 < Real.log (B z) := Real.log_pos hB
    dsimp only [δ]
    positivity
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
  have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H : ℝ)^3)).trans_le hω
  have hden : 0 < 1+ω := by linarith only [hω0]
  have hfactor' (i : Fin b) : B (p.left i)/B z-δ ≤ u i ∧ u i ≤ B (p.left i)/B z :=
    hfactor (p.left i) S (hp3 i) hS hBS hSz (hp i) (hpz i)
  have hcontract' (i : Fin b) (hi : i.val+1 < b) :
      B (p.left ⟨i.val+1,hi⟩)/B z ≤ (B (p.left i)/B z)/(1+ω) := by
    have hh := div_le_div_of_nonneg_right (hcontract i hi) hB0.le
    convert hh using 1
    ring
  have hnormalizedLower (i : Fin b) : 1/(B z)^(1/3 : ℝ) ≤ B (p.left i)/B z := by
    have he : (B z)^(2/3 : ℝ)/B z = 1/(B z)^(1/3 : ℝ) := by
      calc
        _ = (B z)^(2/3 : ℝ)/(B z)^(1 : ℝ) := by rw [Real.rpow_one]
        _ = (B z)^(-(1/3 : ℝ)) := by rw [← Real.rpow_sub hB0]; norm_num
        _ = _ := by rw [Real.rpow_neg hB0.le]; simp only [one_div]
    rw [← he]
    exact div_le_div_of_nonneg_right (hlarge i) hB0.le
  have hnonneg (i : Fin b) : 0 ≤ u i ∧ 0 ≤ v i := by
    have hiH : (i.val : ℝ) ≤ H := by exact_mod_cast (show i.val ≤ H by omega)
    have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hcube : 1 ≤ (H : ℝ)^3 := one_le_pow₀ hHr
    have hthird : 0 < (B z)^(1/3 : ℝ) := Real.rpow_pos_of_pos hB0 _
    have hsmall : (2*(i.val : ℝ)+2)*δ < 1/(B z)^(1/3 : ℝ) := by
      have hsep : (8*(H : ℝ)+20)*δ < 1/(40*(H : ℝ)^3*(B z)^(1/3 : ℝ)) := by
        simpa only [mul_div_assoc] using hseparation H hH hdim
      have hfrac : 1/(40*(H : ℝ)^3*(B z)^(1/3 : ℝ)) ≤ 1/(B z)^(1/3 : ℝ) :=
        one_div_le_one_div_of_le hthird
          (by
            have hh := mul_le_mul_of_nonneg_right hcube hthird.le
            nlinarith only [hh,hthird])
      exact (mul_le_mul_of_nonneg_right (by linarith only [hiH,hHr]) hδ.le).trans_lt
        (hsep.trans_le hfrac)
    have hleft := (hfactor' i).1
    have hlower := hnormalizedLower i
    have hpair := (abs_le.mp (halign i)).2
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    constructor <;> nlinarith only [hsmall,hleft,hlower,hpair,hδ,hi0]
  constructor
  · by_cases hb2 : 1 < b
    · have hhead := prime_coordinate_endpoint_bound (hp3 ⟨0,hb⟩) hz (hpz ⟨0,hb⟩)
      have hhead' : B (p.left ⟨0,hb⟩)/B z ≤ 1+1/B z := by
        apply (div_le_iff₀ hB0).mpr
        have he : (1+1/B z)*B z = B z+1 := by field_simp
        rw [he]
        exact hhead
      have hfirstPrime : B (p.left ⟨1,hb2⟩)/B z ≤ (1+1/B z)/(1+ω) :=
        (hcontract' ⟨0,hb⟩ hb2).trans (div_le_div_of_nonneg_right hhead' hden.le)
      have hround := (collision_grid_enclosure hδ (hnonneg ⟨1,hb2⟩).1
        (hnonneg ⟨1,hb2⟩).2 (halign ⟨1,hb2⟩)).2.2.2.2
      have hrounded : pairedGridUpper δ ((L+U)/(2*B z)) label 1 ≤ 
          B (p.left ⟨1,hb2⟩)/B z+(2*(H : ℝ)+3)*δ := by
        have hcoeff : (5 : ℝ) ≤ 2*(H : ℝ)+3 := by
          have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
          linarith only [hh]
        have hc := mul_le_mul_of_nonneg_right hcoeff hδ.le
        have hf := (hfactor' ⟨1,hb2⟩).2
        simp only [pairedGridUpper,one_ne_zero,ite_false,dite_eq_left hb2]
        dsimp only [label] at hround ⊢
        norm_num only [Nat.cast_one] at hround
        linarith only [hround,hf,hc]
      exact hfirst H ω (B (p.left ⟨1,hb2⟩)/B z)
        (pairedGridUpper δ ((L+U)/(2*B z)) label 1)
        hH hdim hω hω1 hfirstPrime hrounded
    · have he : pairedGridUpper δ ((L+U)/(2*B z)) label 1 = (L+U)/(2*B z) := by
        simp only [pairedGridUpper,one_ne_zero,ite_false,dite_eq_right hb2]
      rw [he]
      exact hterminal L U hLU hU
  · intro i hi
    have hlower := hnormalizedLower i
    have halign' : |u ⟨i.val+1,hi⟩-v ⟨i.val+1,hi⟩| ≤ 
        (2*(i.val : ℝ)+3)*δ := by
      have hh := halign ⟨i.val+1,hi⟩
      change |u ⟨i.val+1,hi⟩-v ⟨i.val+1,hi⟩| ≤ (2*((i.val+1:ℕ):ℝ)+1)*δ at hh
      have he : 2*((i.val+1:ℕ):ℝ)+1=2*(i.val:ℝ)+3 := by push_cast; ring
      rw [he] at hh
      exact hh
    exact hgap H i.val (B (p.left i)/B z) (B (p.left ⟨i.val+1,hi⟩)/B z)
      (u i) (u ⟨i.val+1,hi⟩) ω hH hdim (show i.val ≤ H by omega)
      hlower hω hω1 (hcontract' i hi) (hfactor' i).1 (hfactor' _).2
      (v i) (v ⟨i.val+1,hi⟩) (halign i) halign'

end TotientAsymptotic

end

end OAI
