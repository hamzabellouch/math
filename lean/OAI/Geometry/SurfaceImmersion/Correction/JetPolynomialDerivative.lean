import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialAlgebra

namespace OAI

/-! Differentiation preserves finite polynomial dependence on higher jets.
The proof is for actual derivatives, including the low-jet chain rule. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

def sumList {ι : Type*} : List ι → (ι → Expression) → Expression
  | [], _ => .coeff (fun _ => 0)
  | i :: l, f => .add (f i) (sumList l f)

lemma eval_sumList {ι : Type*} (l : List ι) (f : ι → Expression) (G : Base → Space)
    (z : Base × ℝ) : (sumList l f).eval G z = (l.map (fun i => (f i).eval G z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, eval, List.map_cons, List.sum_cons, ih]

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → Expression) (N : ℕ)
    (hN : 2 ≤ N) (hf : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (hf i (List.mem_cons_self ..))
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

lemma loss_sumList_le {ι : Type*} (l : List ι) (f : ι → Expression) (N : ℕ)
    (hf : ∀ i ∈ l, (f i).loss ≤ N) : (sumList l f).loss ≤ N := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih =>
    exact max_le (hf i (List.mem_cons_self ..))
      (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → Expression)
    (hf : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨hf i (List.mem_cons_self ..),
      ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))⟩

def lowFactor (v : Fin 2) : LowIndex → Expression
  | .inl i => .coeff (fun _ => coordinateVector v i)
  | .inr (w, a) => .atom (v :: lowWord w) a (.coeff (fun _ => 1))

lemma eval_lowFactor (v : Fin 2) (i : LowIndex) (G : Base → Space) (z : Base × ℝ) :
    (lowFactor v i).eval G z = lowDerivative G v z.1 i := by
  cases i with
  | inl i => rfl
  | inr i => simp [lowFactor, eval, lowDerivative]

lemma order_lowFactor (v : Fin 2) (i : LowIndex) : (lowFactor v i).order ≤ 3 := by
  cases i with
  | inl i => simp [lowFactor, order]
  | inr i =>
    obtain ⟨w, a⟩ := i
    have h : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    simp only [lowFactor, order, List.length_cons]
    omega

lemma loss_lowFactor (v : Fin 2) (i : LowIndex) : (lowFactor v i).loss ≤ 1 := by
  cases i with
  | inl i => simp [lowFactor, loss]
  | inr i =>
    obtain ⟨w, a⟩ := i
    have h : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    simp only [lowFactor, loss, List.length_cons]
    omega

lemma smoothCoeffs_lowFactor (O : Set LowJet) (v : Fin 2) (i : LowIndex) :
    (lowFactor v i).SmoothCoeffs O := by
  cases i with
  | inl i => exact contDiffOn_const
  | inr i => exact contDiffOn_const

/-- The chain rule differentiates smooth low-jet coefficients and introduces
one additional actual jet factor. -/
def slow (v : Fin 2) : Expression → Expression
  | .coeff c => sumList Finset.univ.toList (fun i : LowIndex =>
      (lowFactor v i).mul (.coeff (slowDerivative c (lowBasis i))))
  | .atom w a e => .add (.atom (v :: w) a e) (.atom w a (slow v e))
  | .add e f => .add (slow v e) (slow v f)

lemma smoothCoeffs_slow {O : Set LowJet} (hO : IsOpen O) (v : Fin 2)
    {e : Expression} (he : e.SmoothCoeffs O) : (e.slow v).SmoothCoeffs O := by
  induction e with
  | coeff c =>
    apply smoothCoeffs_sumList
    intro i _
    exact smoothCoeffs_mul (smoothCoeffs_lowFactor O v i)
      (LocalPeriodicCalculus.slow_smooth hO he (lowBasis i))
  | atom w a e ih => exact ⟨he, ih he⟩
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

lemma order_slow_le (v : Fin 2) (e : Expression) :
    (e.slow v).order ≤ max 3 (e.order + 1) := by
  induction e with
  | coeff c =>
    apply order_sumList_le _ _ _ (by simp [order])
    intro i _
    exact (order_mul_le _ _).trans (max_le (order_lowFactor v i) (by simp [order]))
  | atom w a e ih => simp only [slow, order, List.length_cons] at *; omega
  | add e f ihe ihf => simp only [slow, order] at *; omega

lemma loss_slow_le (v : Fin 2) (e : Expression) : (e.slow v).loss ≤ e.loss + 1 := by
  induction e with
  | coeff c =>
    apply loss_sumList_le
    intro i _
    exact (loss_mul_le _ _).trans (by simpa only [loss, add_zero] using loss_lowFactor v i)
  | atom w a e ih => simp only [slow, loss, List.length_cons] at *; omega
  | add e f ihe ihf => simp only [slow, loss] at *; omega

lemma coefficient_chain_rule_joint {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {c : LowJet × ℝ → ℝ}
    (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)) (v : Fin 2) (p : Base)
    (hp : lowJet G p ∈ O) (t : ℝ) :
    fderiv ℝ (fun q => c (lowJet G q, t)) p (coordinateVector v) =
      ∑ i : LowIndex, lowDerivative G v p i * slowDerivative c (lowBasis i) (lowJet G p, t) := by
  have hs : DifferentiableAt ℝ (fun Q : LowJet => c (Q, t)) (lowJet G p) :=
    ((hc.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp _
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
  simpa only [smul_eq_mul, LocalPeriodicCalculus.fderiv_slice hO hc hp] using
    coefficient_chain_rule hG v p hs

/-- The syntactic derivative evaluates to the genuine derivative on every
open region where the low-jet coefficients are smooth. -/
theorem eval_slow {O : Set LowJet} {S : Set Base} (hO : IsOpen O) (hS : IsOpen S)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (v : Fin 2) {e : Expression} (he : e.SmoothCoeffs O) {p : Base} (hp : p ∈ S) (t : ℝ) :
    (e.slow v).eval G (p, t) = fderiv ℝ (fun q => e.eval G (q, t)) p (coordinateVector v) := by
  induction e with
  | coeff c =>
    rw [slow, eval_sumList, ← List.sum_toFinset _ Finset.univ.nodup_toList,
      Finset.toList_toFinset]
    simp only [eval_mul, eval_lowFactor, eval]
    exact (coefficient_chain_rule_joint hO hG he v p (hQ hp) t).symm
  | atom w a e ih =>
    have hj := (jet_smooth hG w a).differentiable (by simp) p
    have he' : DifferentiableAt ℝ (fun q => e.eval G (q, t)) p :=
      (((eval_smooth hG hQ (e := e) he).contDiffAt
        ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
    simp only [slow, eval, ih he]
    rw [fderiv_fun_mul hj he']
    simp only [add_apply, smul_apply, smul_eq_mul,
      jet_cons]
    ring
  | add e f ihe ihf =>
    have hd (g : Expression) (hg : g.SmoothCoeffs O) :
        DifferentiableAt ℝ (fun q => g.eval G (q, t)) p :=
      (((eval_smooth hG hQ hg).contDiffAt
        ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
    simpa only [slow, eval, fderiv_fun_add (hd e he.1) (hd f he.2),
      add_apply] using congrArg₂ (· + ·) (ihe he.1) (ihf he.2)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
