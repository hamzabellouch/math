import OAI.NumberTheory.TotientAsymptotic.PPTWitnessCount

namespace OAI

/-! Build a counted grid witness from an actual regular totient preimage. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- The large-head conclusion used by the comparison also places the
first prime above every terminal window. -/
theorem ppt_large_head_above_terminal : ∀ᶠ z : ℝ in atTop,
    ∀ p : ℕ, z^(9/10:ℝ) ≤ p → 2*(B z)^(2/3:ℝ) < B p := by
  filter_upwards [B_tendsto.eventually ppt_smooth_height_half_scale,
    B_tendsto.eventually (eventually_ge_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)]
    with z hsmall hB hz
  intro p hhead
  have hz0 : 0 < z := zero_lt_one.trans hz
  have ht : 0 < B z := (by norm_num : (0:ℝ) < 2).trans_le hB
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hz0 _) hhead
  rw [Real.log_rpow hz0] at hlog
  have hdouble := Real.log_le_log (mul_pos (by norm_num : (0:ℝ) < 9/10) (Real.log_pos hz)) hlog
  rw [Real.log_mul (by norm_num : (9/10:ℝ)≠0) (Real.log_pos hz).ne'] at hdouble
  change Real.log (9/10:ℝ)+B z ≤ B p at hdouble
  have hlogfrac : -1 ≤ Real.log (9/10:ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 9/10)
    norm_num at hh ⊢
    linarith only [hh]
  have hT : 1 ≤ (B z)^(2/3:ℝ) := Real.one_le_rpow (by linarith only [hB]) (by norm_num)
  have hh := hsmall (Real.exp (Real.exp ((B z)^(2/3:ℝ))))
    (by rw [B_exp_exp]; linarith only [hT])
  rw [B_exp_exp] at hh
  linarith only [hh,hT,hdouble,hlogfrac]

/-- The finite label cutoff contains every actual prime whose
predecessor divides a value in the current comparison interval. -/
theorem ppt_prime_in_label_range : ∀ᶠ z : ℝ in atTop,
    ∀ p : ℕ, 3 ≤ p → (p-1:ℕ) ≤ z → p ≤ discardPrimeBound (B z) := by
  filter_upwards [B_tendsto.eventually (eventually_ge_atTop (5:ℝ)),
    eventually_ge_atTop (Real.exp 1)] with z hB hz
  intro p hp hpz
  have hcoord := prime_coordinate_endpoint_bound hp hz hpz
  have hlp : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hcut := (discardPrimeBound_bounds (by linarith only [hB])).2.2.2
  have hheight : B p ≤ (6/5:ℝ)*B z := by linarith only [hcoord,hB]
  have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hheight)
  rw [exp_exp_doubleLog hlp] at hh
  exact_mod_cast hh.trans hcut

lemma ppt_nonhead_product_succ {k : ℕ} (p : Fin (k+1) → ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (k+1) => 0 < i.val),p i)=∏ i:Fin k,p i.succ := by
  classical
  symm
  apply Finset.prod_bij (fun i _=>i.succ)
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩
  · intro i _ j _ hij
    exact Fin.succ_injective _ hij
  · intro j hj
    have hj0 : 0 < j.val := (Finset.mem_filter.mp hj).2
    refine ⟨j.pred (by intro h; subst j; simp at hj0),Finset.mem_univ _,?_⟩
    exact Fin.succ_pred _ _
  · intro i _
    rfl

/-- Every nonleading product in the actual contracting list is a small
power of the local endpoint. This pays for the common canceled factor. -/
theorem ppt_contracted_nonhead_product {A : ℝ} (hA : 0 < A) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in atTop,∀ (N H : ℕ) (p : Fin N → ℕ) (ω : ℝ),∀ hN : 0 < N,
      (∀ i,(p i).Prime) → (∀ i,3 ≤ p i) → 1 ≤ H → N ≤ H →
      (H:ℝ) ≤ A*Real.log (B z) → 1/(10*(H:ℝ)^3) ≤ ω → ω ≤ 1 →
      (∀ i:Fin N,0 < i.val → B (p i) ≤ B (p ⟨0,hN⟩)/(1+ω)) →
      (p ⟨0,hN⟩-1:ℕ) ≤ z →
      (((∏ i ∈ Finset.univ.filter (fun i:Fin N=>0 < i.val),p i):ℕ):ℝ) ≤ z^ε := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [B_tendsto.eventually (ppt_local_contracted_first_loss hA),
    ppt_prime_product_subpower_of_gap hA.le hγ hε,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ)),
    eventually_ge_atTop (Real.exp 1)] with z hgap hsmall hB hz
  intro N H p ω hN hp hp3 hH hNH hdim hω hω1 hcontract hpred
  cases N with
  | zero => omega
  | succ k =>
    have ht : 0 < B z := zero_lt_one.trans hB
    have hH0 : (0:ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
    have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H:ℝ)^3)).trans_le hω
    have hden : 0 < 1+ω := by linarith only [hω0]
    have hhead := prime_coordinate_endpoint_bound (hp3 0) hz hpred
    rw [ppt_nonhead_product_succ]
    apply hsmall k (fun i=>p i.succ) (fun i=>hp i.succ)
      ((Nat.cast_le.mpr (show k ≤ H by omega)).trans hdim)
    intro i
    have hu : B (p i.succ)/B z ≤ (1+1/B z)/(1+ω) := by
      calc
        _ ≤ (B (p 0)/(1+ω))/B z :=
          div_le_div_of_nonneg_right (hcontract i.succ (by simp)) ht.le
        _ ≤ ((B z+1)/(1+ω))/B z :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hhead hden.le) ht.le
        _ = _ := by field_simp
    have hpad : B (p i.succ)/B z ≤ B (p i.succ)/B z+
        (2*(H:ℝ)+3)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by
      have hl : 0 ≤ Real.log (B z) := (Real.log_pos hB).le
      have he : 0 ≤ (2*(H:ℝ)+3)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by positivity
      linarith only [he]
    have hh := hgap H ω (B (p i.succ)/B z) (B (p i.succ)/B z)
      hH hdim hω hω1 hu hpad
    have hh' := (div_le_iff₀ ht).mp hh
    convert hh' using 1
    ring

/-- An actual regular alternative preimage produces the finite grid
witness consumed by the counting theorem. This is the suffix case, in
which the candidate head itself belongs to the geometric row. -/
theorem ppt_regular_geometric_witness (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n N H F r : ℕ) (p : Fin N → ℕ) (v : Fin n → ℝ)
      (ι : Fin N ↪o Fin n) (budget c S : ℝ),∀ hN : 0 < N,
      n ≤ m → N ≤ H → (H:ℝ) ≤ A*Real.log (B z) → m-(ι ⟨0,hN⟩).val ≤ H →
      v∈relaxedGeometricFamily m n budget c → (∀ i,v (ι i)=B (p i)) →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H:ℝ)^4 →
      (∀ i,IsNormalPrime S (p i)) → (∀ i,3 ≤ p i) → StrictAnti p →
      0 < F → F.totient=d*r.totient → r=∏ i,p i →
      (largestPrimeFactor d:ℝ) ≤ S → SquarefreeAbove F S → SquarefreeAbove F.totient S →
      (∀ q:ℕ,q.Prime → q∣F → IsNormalPrime S q) →
      largestPrimeFactor F≠p ⟨0,hN⟩ → (∀ i,(p i-1:ℕ) ≤ z) → (F.totient:ℝ) ≤ z →
      z^(9/10:ℝ) ≤ p ⟨0,hN⟩ → Nonempty (PPTResidualGridWitness d N H z S A r) := by
  filter_upwards [ppt_regular_preimage_terminal hA, ppt_selected_grid_data d hd hA,
    ppt_large_head_above_terminal,ppt_prime_in_label_range,
    ppt_contracted_nonhead_product hA (1/10) (by norm_num),
    B_tendsto.eventually ppt_smooth_height_half_scale,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ))]
    with z hterminal hselected hheadLarge hprimeRange hnonhead hsmall hB
  intro m n N H F r p v ι budget c S hN hnm hNH hdim hremaining hgeom hcoords
    hS hheight hp hp3 hpa hF hvalue hr hseed hsqF hsqPhi hnormal hmismatch hpz hsize hhead
  have ht : 0 < B z := zero_lt_one.trans hB
  have hH : 1 ≤ H := by omega
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hS2 : 2 ≤ S := by
    have he : 2 < Real.exp 1 := by linarith only [Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)]
    have hexp : Real.exp 1 < Real.exp (Real.exp 1) := Real.exp_lt_exp.mpr (by linarith only [he])
    exact (he.trans hexp).le.trans hS
  have hBS : 0 ≤ B S := by
    have hh := ppt_B_mono (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS
    have hh' : (1 : ℝ) ≤ B S := by simpa only [B,Real.log_exp] using hh
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hh'
  have hvalue' : F.totient=d*(∏ i,p i).totient := by rw [←hr]; exact hvalue
  obtain ⟨j,J,hL,hU,⟨hJ,hJN⟩,hLU,hhigh,hlow,hbudget,
    Q,q,E,hJQ,hSL,hE,hES,hqa,hq,heq,hfirst,hptail,hqhigh,hqtail,hqz⟩ :=
    hterminal N H d F p S hN hd hF hNH hdim hS2 hBS hheight hp hp3 hpa
      hvalue' hseed hsqF hnormal hmismatch hpz hsize (hheadLarge _ hhead)
  let L := (B z)^(2/3:ℝ)+2*(j.val:ℝ)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))
  let U := (B z)^(2/3:ℝ)+(2*(j.val:ℝ)+1)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))
  let V := Real.exp (Real.exp ((L+U)/2))
  have hSV : S ≤ V := hSL.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
    (by linarith only [hLU])))
  have hUt : 2*(B z)^(2/3:ℝ) ≤ B z := by
    have hT : 0 ≤ (B z)^(2/3:ℝ) := Real.rpow_nonneg ht.le _
    have hh := hsmall (Real.exp (Real.exp ((B z)^(2/3:ℝ))))
      (by rw [B_exp_exp]; linarith only [hT])
    rw [B_exp_exp] at hh
    linarith only [hh,ht,hT]
  have hVz : V ≤ z := by
    have hh : (L+U)/2 ≤ B z := by linarith only [hLU,hU,hUt]
    have he := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hh)
    have hz1 : 1 < z := by
      have hh := (hpz ⟨0,hN⟩)
      have hp0 := hp3 ⟨0,hN⟩
      have htwo : (2:ℝ) ≤ (p ⟨0,hN⟩-1:ℕ) := by exact_mod_cast (show 2 ≤ p ⟨0,hN⟩-1 by omega)
      linarith only [hh,htwo]
    simpa only [V,exp_exp_doubleLog hz1] using he
  have hcontract := ppt_geometric_embedded_contraction hgeom hnm ι hN hremaining
  let ω : ℝ := 1/(10*(H:ℝ)^3)
  have hnonheadContract (i : Fin N) (hi : 0 < i.val) :
      B (p i) ≤ B (p ⟨0,hN⟩)/(1+ω) := by
    have hh := hcontract.2 ⟨0,hN⟩ i (show (⟨0,hN⟩:Fin N) < i from hi)
    simpa only [hcoords] using hh
  have hnonheadBound := hnonhead N H p ω hN (fun i=>(hp i).1) hp3 hH hNH hdim le_rfl
    hcontract.1 hnonheadContract (hpz ⟨0,hN⟩)
  have htargetSize : ((d*r.totient:ℕ):ℝ) ≤ z := by rw [←hvalue]; exact hsize
  have htargetSq : SquarefreeAbove (d*r.totient) S := by rw [←hvalue]; exact hsqPhi
  have hdiscard : 0 ≤ (2*(H:ℝ)+1)*Real.sqrt (B S*B z)+B S := by positivity
  have hgridBudget : (8*(H:ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 := by
    linarith only [hbudget,hdiscard]
  obtain ⟨b,h,s,cc,a,pair,tail,grid,hb,hbH,hhH,hmem,hatail,htailinj,htail,
    hreal,hparams,hconditions,hExp⟩ :=
    hselected m n N Q J H E r j.val p q v ι budget c S L U V hJ hJN hJQ
      hnm hNH ((Nat.lt_succ_iff.mp j.isLt).trans hNH) hdim hremaining hgeom hcoords
      hS hheight rfl hSV hVz hL hLU hU hseed hp (fun i=>(hq i).1) hp3 (fun i=>(hq i).2)
      hpa hqa (hfirst hJ) hr heq hE hES hhigh (fun i hi=>(hqhigh i hi).le)
      hptail hqtail hpz hqz htargetSize htargetSq (fun i=>hprimeRange _ (hp3 i) (hpz i))
      hnonheadBound hhead hgridBudget
  let ell := pptResidualLabel b h s cc a j.val grid
  have hterm : pptLabelTerminal z N ell=V := rfl
  have htermheight : 0 ≤ B (pptLabelTerminal z N ell) ∧
      B (pptLabelTerminal z N ell) ≤ 2*(B z)^(2/3:ℝ) := by
    rw [hterm]
    change 0 ≤ B (Real.exp (Real.exp ((L+U)/2))) ∧ _
    rw [B_exp_exp]
    have hL0 : 0 ≤ L := (Real.rpow_nonneg ht.le _).trans hL
    constructor <;> linarith only [hL0,hLU,hU]
  have hterminalEq : comparisonCutoffs z (pptLabelUpper z N ell) (pptLabelB ell)=
      pptLabelTerminal z N ell := by
    change comparisonCutoffs z
      (pairedGridUpper (2*((Real.log (B z))^5/Real.sqrt (B z))) ((L+U)/(2*B z)) grid) b=V
    rw [comparisonCutoffs,show pairedGridUpper (2*((Real.log (B z))^5/Real.sqrt (B z)))
      ((L+U)/(2*B z)) grid b=(L+U)/(2*B z) by
        simp [pairedGridUpper,show b≠0 by omega]]
    dsimp only [V]
    congr 2
    field_simp
  exact ⟨{
    label := ell
    length_pos := hb
    length_le := hbH
    tail_length_le := hhH
    label_mem := hmem
    terminal_normality := hSV
    terminal_height := htermheight
    terminal_eq := hterminalEq
    tail := tail
    tail_product := hatail
    tail_injective := htailinj
    tail_normal := fun i=>(htail i).1
    tail_smooth := fun i=>(htail i).2
    pair := pair
    recovery := hreal
    parameters := hparams
    conditions := hconditions
    exponent := hExp
  }⟩

/-- Count an arbitrary finite subset of regular residual values using
their actual chosen preimages and geometric prime lists. This form is
independent of the ambient candidate family and applies to every dyadic
layer of the regular suffix set. -/
theorem ppt_regular_geometric_count (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n N H : ℕ) (budget c S : ℝ) (R : Finset ℕ)
      (F : ℕ→ℕ) (p : ℕ→Fin N→ℕ) (v : ℕ→Fin n→ℝ)
      (ι : ℕ→Fin N↪o Fin n),∀ hN : 0 < N,
      n ≤ m → N ≤ H → (H:ℝ) ≤ A*Real.log (B z) →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H:ℝ)^4 → (largestPrimeFactor d:ℝ) ≤ S →
      (∀ r∈R,m-(ι r ⟨0,hN⟩).val ≤ H) →
      (∀ r∈R,v r∈relaxedGeometricFamily m n budget c) →
      (∀ r∈R,∀ i,v r (ι r i)=B (p r i)) →
      (∀ r∈R,∀ i,IsNormalPrime S (p r i)) →
      (∀ r∈R,∀ i,3 ≤ p r i) → (∀ r∈R,StrictAnti (p r)) →
      (∀ r∈R,0 < F r ∧ (F r).totient=d*r.totient ∧ r=∏ i,p r i) →
      (∀ r∈R,SquarefreeAbove (F r) S ∧ SquarefreeAbove (F r).totient S) →
      (∀ r∈R,∀ q:ℕ,q.Prime → q∣F r → IsNormalPrime S q) →
      (∀ r∈R,largestPrimeFactor (F r)≠p r ⟨0,hN⟩) →
      (∀ r∈R,∀ i,(p r i-1:ℕ) ≤ z) → (∀ r∈R,((F r).totient:ℝ) ≤ z) →
      (∀ r∈R,z^(9/10:ℝ) ≤ p r ⟨0,hN⟩) →
      (R.card:ℝ) ≤ z/((d:ℝ)*Real.log z)*(B z)^(-K) := by
  filter_upwards [ppt_regular_geometric_witness d hd hA,
    ppt_witnessed_residual_count d hd hA K] with z hwitness hcount
  intro m n N H budget c S R F p v ι hN hnm hNH hdim hS hheight hseed hremaining
    hgeom hcoords hp hp3 hpa hvalue hsq hnormal hmismatch hpz hsize hhead
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBS : 0 ≤ B S := by
    have hh := ppt_B_mono (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS
    have hh' : (1 : ℝ) ≤ B S := by simpa only [B,Real.log_exp] using hh
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hh'
  apply hcount N H S R hdim hS1 hBS
  intro r hr
  exact hwitness m n N H (F r) r (p r) (v r) (ι r) budget c S hN hnm hNH hdim
    (hremaining r hr) (hgeom r hr) (hcoords r hr) hS hheight (hp r hr) (hp3 r hr)
    (hpa r hr) (hvalue r hr).1 (hvalue r hr).2.1 (hvalue r hr).2.2 hseed
    (hsq r hr).1 (hsq r hr).2 (hnormal r hr) (hmismatch r hr) (hpz r hr)
    (hsize r hr) (hhead r hr)

end TotientAsymptotic

end

end OAI
