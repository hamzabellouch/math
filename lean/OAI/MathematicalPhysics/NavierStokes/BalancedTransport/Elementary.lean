import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericAlgebra

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

def Elementary {d : ℕ} [NeZero d] (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ p : NumericProgram, p ≠ [] ∧ p.Closed ∧ (∀ x : Fin d → ℝ, p.Valid x) ∧ p.real = f

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e] {f g : (Fin d → ℝ) → ℝ}

lemma literal (q : ℚ) : Elementary (fun _ : Fin d → ℝ => (q : ℝ)) :=
  ⟨NumericProgram.literal q, by simp [NumericProgram.literal],
    NumericProgram.literal_closed q, NumericProgram.literal_valid q, rfl⟩

lemma coordinate (k : Fin d) : Elementary (fun z : Fin d → ℝ => z k) :=
  ⟨NumericProgram.coordinate k, by simp [NumericProgram.coordinate],
    NumericProgram.coordinate_closed k, NumericProgram.coordinate_valid k,
    funext (NumericProgram.coordinate_real k)⟩

lemma add (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x + g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 2 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 2 p q hpc hqc hpn hqn (Or.inl rfl),
    fun x => NumericProgram.binary_valid 2 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_add_real p q hqc hqn)⟩

lemma mul (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x * g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 3 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 3 p q hpc hqc hpn hqn (Or.inr rfl),
    fun x => NumericProgram.binary_valid 3 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_mul_real p q hqc hqn)⟩

lemma neg (hf : Elementary f) : Elementary (fun x => -f x) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 4 0 p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 4 0 p hc hn (Or.inl rfl),
    fun x => NumericProgram.unary_valid 4 0 p x (hv x) (by simp), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma sub (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma inv (hf : Elementary f) (n : ℕ) (hn : ∀ x, ((n+1:ℕ):ℝ)⁻¹ ≤ f x) :
    Elementary (fun x => (f x)⁻¹) := by
  obtain ⟨p, hne, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 5 n p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 5 n p hc hne (Or.inr (Or.inl rfl)),
    fun x => NumericProgram.unary_valid 5 n p x (hv x) (fun _ => hn x), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma exp (hf : Elementary f) : Elementary (fun x => Real.exp (f x)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 7 0 p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 7 0 p hc hn (Or.inr (Or.inr rfl)),
    fun x => NumericProgram.unary_valid 7 0 p x (hv x) (by simp), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma rho (n : ℕ) (hf : Elementary f) : Elementary (fun x => rhoJet n (f x)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p ++ [(6,0,n,0)], by simp, ?_, ?_, ?_⟩
  · apply (NumericProgram.scopedFrom_concat _ _ _).mpr
    exact ⟨hc, ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.right] using List.length_pos_iff.mpr hn, trivial⟩⟩
  · intro x
    exact (NumericProgram.validFrom_concat _ _ _ _).mpr ⟨hv x, ⟨by simp [NumericOp.Valid, NumericOp.tag], trivial⟩⟩
  · funext x
    simp only [NumericProgram.real, NumericProgram.realFrom_concat]
    rfl

lemma logLiteral (q : ℚ) : Elementary (fun _ : Fin d → ℝ => if 0 < q then Real.log (q : ℝ) else 0) := by
  refine ⟨[(8,q,0,0)], by simp, by simp [NumericProgram.Closed, NumericProgram.ScopedFrom, NumericOp.Scoped, NumericOp.tag], ?_, rfl⟩
  intro x
  exact ⟨by simp [NumericOp.Valid, NumericOp.tag], trivial⟩

lemma log_rat {q : ℚ} (hq : 0 < q) : Elementary (fun _ : Fin d → ℝ => Real.log (q : ℝ)) := by
  simpa only [ite_eq_left hq] using (logLiteral (d := d) q)

lemma differentiable (hf : Elementary f) : Differentiable ℝ f := by
  obtain ⟨p, _, _, hv, rfl⟩ := hf
  exact fun x => p.differentiableAt x (hv x)

lemma coordinateDerivative (hf : Elementary f) (k : Fin d) :
    Elementary (fun x => fderiv ℝ f x (Pi.single k 1)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p.jetStep k, ?_, p.jetStep_closed k hc, fun x => p.jetStep_valid k (hv x), ?_⟩
  · apply List.length_pos_iff.mp
    rw [NumericProgram.jetStep_length]
    exact Nat.mul_pos (by decide) (List.length_pos_iff.mpr hn)
  · funext x
    exact p.jetStep_real k x (hv x)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → ℝ)
    (hf : ∀ i ∈ s, Elementary (f i)) : Elementary (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (literal (d := d) 0)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma prod {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → ℝ)
    (hf : ∀ i ∈ s, Elementary (f i)) : Elementary (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (literal (d := d) 1)
  | @insert a s ha ih =>
    simpa only [Finset.prod_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).mul (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e]

lemma zero : Elementary (fun _ : Fin d → ℝ => (0 : ℝ)) := by simpa using (literal (d := d) 0)

lemma one : Elementary (fun _ : Fin d → ℝ => (1 : ℝ)) := by simpa using (literal (d := d) 1)

lemma const_nat (n : ℕ) : Elementary (fun _ : Fin d → ℝ => (n : ℝ)) := by
  simpa using literal (d := d) (n : ℚ)

lemma div_rat (q : ℚ) {f : (Fin d → ℝ) → ℝ} (hf : Elementary f) :
    Elementary (fun x => f x / (q : ℝ)) := by
  simpa [div_eq_mul_inv] using hf.mul (literal q⁻¹)

lemma operation (o : NumericOp) (g : (Fin d → ℝ) → (Fin e → ℝ))
    (s : (Fin d → ℝ) → List ℝ)
    (hg : ∀ k, Elementary (fun x => g x k))
    (hs : ∀ n, Elementary (fun x => (s x).getD n 0))
    (hv : ∀ x, o.Valid (s x)) : Elementary (fun x => o.real e (g x) (s x)) := by
  rcases o with ⟨j,q,a,b⟩
  fin_cases j <;> dsimp only [NumericOp.real, NumericOp.tag, NumericOp.rat,
    NumericOp.left, NumericOp.right]
  · exact literal q
  · exact hg _
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · exact (hs a).inv b (fun x => hv x rfl)
  · exact (hs b).rho a
  · exact (hs a).exp
  · exact logLiteral q

lemma program_registers (p : NumericProgram)
    (g : (Fin d → ℝ) → (Fin e → ℝ)) (s : (Fin d → ℝ) → List ℝ)
    (hg : ∀ k, Elementary (fun x => g x k))
    (hs : ∀ n, Elementary (fun x => (s x).getD n 0))
    (hv : ∀ x, p.ValidFrom (g x) (s x)) :
    ∀ n, Elementary (fun x => (p.realFrom (g x) (s x)).getD n 0) := by
  induction p generalizing s with
  | nil => exact hs
  | cons o p ih =>
    apply ih (fun x => o.real e (g x) (s x) :: s x)
    · intro n
      cases n with
      | zero => exact operation o g s hg hs (fun x => (hv x).1)
      | succ n => exact hs n
    · exact fun x => (hv x).2

lemma comp {f : (Fin e → ℝ) → ℝ} (hf : Elementary f)
    (g : (Fin d → ℝ) → (Fin e → ℝ))
    (hg : ∀ k, Elementary (fun x => g x k)) : Elementary (fun x => f (g x)) := by
  obtain ⟨p, _, _, hv, rfl⟩ := hf
  exact program_registers p g (fun _ => []) hg (fun n => by simpa using (zero (d:=d)))
    (fun x => hv (g x)) 0

lemma smoothTransition {f : (Fin d → ℝ) → ℝ} (hf : Elementary f) :
    Elementary (fun x => Real.smoothTransition (f x)) := by
  have hρ : Elementary (fun x => expNegInvGlue (f x)) := by
    simpa only [rhoJet_zero] using hf.rho 0
  have hρ' : Elementary (fun x => expNegInvGlue (1 - f x)) := by
    simpa only [rhoJet_zero] using (one.sub hf).rho 0
  have hi := (hρ.add hρ').inv 8 (fun x => by
    simpa using transition_denom_lower (f x))
  simpa only [Real.smoothTransition, div_eq_mul_inv] using hρ.mul hi

end BalancedTransport.Effectivity.Elementary
end

end OAI
