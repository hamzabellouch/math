import OAI.InformationTheory.QuantumCircuit.ApproximationBudget
import OAI.InformationTheory.QuantumCircuit.CommonAxes

namespace OAI

/-! Low-degree approximation of products of reflections. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

def propagationBudget (N ell : ℕ) : ℝ :=
  ((ell + 1 : ℕ) : ℝ) * (3 * N : ℝ) ^ ell * (9 : ℝ) ^ ell

lemma propagationBudget_nonneg (N ell : ℕ) : 0 ≤ propagationBudget N ell := by
  unfold propagationBudget
  positivity

lemma conjugate_complex_list_sum {N : ℕ} {ι : Type*} (U : Operator N)
    (l : List ι) (c : ι → ℂ) (D : ι → Operator N) :
    conjugate U (l.map (fun i => c i • D i)).sum =
      (l.map (fun i => c i • conjugate U (D i))).sum := by
  simp only [conjugate, ← List.sum_map_mul_left, ← List.sum_map_mul_right,
    mul_smul_comm, smul_mul_assoc]

lemma subcount_sandwich_approximation
    (hspec : PublishedProductSpectralResolution) {N : ℕ}
    (ψ : State N) (hψ : ‖ψ‖ ≤ 1) (M A B : Count N)
    (hA : A.Subcount M) (hB : B.Subcount M)
    (J : Finset (Fin N)) (D : Operator N) (hD : TensorSupported J D)
    (hDn : ‖D‖ ≤ 1) (p : Polynomial ℝ) (r δ τ : ℝ)
    (hδ : 0 ≤ δ) (hp0 : p.eval 0 = 1)
    (hp : ∀ k : ℕ, 1 ≤ k → (k : ℝ) < r → |p.eval (k : ℝ)| ≤ δ)
    (htail : ‖act (M.high r) ψ‖ ≤ τ) :
    ApproxOn ψ ((J.card : ℝ) + p.natDegree) (weight N p)
      (δ + (1 + weight N p) * τ) (A.zero * D * B.zero) := by
  have hz : A.zero * D * B.zero =
      (M.restrict A.support).zero * D * (M.restrict B.support).zero :=
    congrArg₂ (fun X Y : Operator N => X * D * Y) hA.zero_eq hB.zero_eq
  rw [hz]
  exact sandwich_approximation ψ M J A.support B.support D hD hDn p r δ τ hδ hψ hp0 hp
    ((M.restrict_high_action_le hspec _ r ψ).trans htail)

lemma reflection_expansion_approximation
    (hspec : PublishedProductSpectralResolution) {N : ℕ}
    (l : List (Count N)) (hl : l.Pairwise (fun A B => Disjoint A.support B.support))
    (ψ : State N) (hψ : ‖ψ‖ ≤ 1)
    (J : Finset (Fin N)) (D : Operator N) (hD : TensorSupported J D)
    (hDn : ‖D‖ ≤ 1) (p : Polynomial ℝ) (r δ τ : ℝ)
    (hδ : 0 ≤ δ) (hp0 : p.eval 0 = 1)
    (hp : ∀ k : ℕ, 1 ≤ k → (k : ℝ) < r → |p.eval (k : ℝ)| ≤ δ)
    (htail : ‖act ((jointTest l).high r) ψ‖ ≤ τ) :
    ApproxOn ψ ((J.card : ℝ) + p.natDegree) ((9 : ℝ)^l.length * weight N p)
      ((9 : ℝ)^l.length * (δ + (1 + weight N p) * τ))
      (conjugate (reflectList l) D) := by
  let W := weight N p
  let ε := δ + (1 + W) * τ
  have hpair : ∀ a ∈ reflectionTerms l, ∀ b ∈ reflectionTerms l,
      ApproxOn ψ ((J.card : ℝ) + p.natDegree) W ε (a.2.zero * D * b.2.zero) := by
    intro a ha b hb
    exact subcount_sandwich_approximation hspec ψ hψ (jointTest l) a.2 b.2
      (reflectionTerms_subcount l (jointTest l) (jointTest_subcount l hl) a ha)
      (reflectionTerms_subcount l (jointTest l) (jointTest_subcount l hl) b hb)
      J D hD hDn p r δ τ hδ hp0 hp htail
  rw [reflection_double_expansion l hl]
  have hdouble := approx_real_list_sum ψ (reflectionTerms l) Prod.fst
    (fun a => ((reflectionTerms l).map (fun b => b.1 • (a.2.zero * D * b.2.zero))).sum)
    ((J.card : ℝ) + p.natDegree)
    (((reflectionTerms l).map (fun a => |a.1|)).sum * W)
    (((reflectionTerms l).map (fun a => |a.1|)).sum * ε)
    (fun a ha => approx_real_list_sum ψ (reflectionTerms l) Prod.fst
      (fun b => a.2.zero * D * b.2.zero) _ W ε (hpair a ha))
  rw [reflectionTerms_weight] at hdouble
  have hpow : (3 : ℝ)^l.length * (3 : ℝ)^l.length = (9 : ℝ)^l.length := by
    rw [← mul_pow]; norm_num
  simpa only [← mul_assoc, hpow] using hdouble

lemma tensor_reflection_approximation
    (hspec : PublishedProductSpectralResolution) {N ell : ℕ}
    (R : ReflectionLayer N) (ψ : State N) (hψ : ‖ψ‖ ≤ 1)
    (J : Finset (Fin N)) (hJ : J.card ≤ ell)
    (D : Operator N) (hD : TensorSupported J D) (hDn : ‖D‖ ≤ 1)
    (p : Polynomial ℝ) (r δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (hp0 : p.eval 0 = 1)
    (hp : ∀ k : ℕ, 1 ≤ k → (k : ℝ) < r → |p.eval (k : ℝ)| ≤ δ)
    (htail : ∀ S : List (Count N), S.Sublist R.gates → S.length ≤ ell →
      ‖act ((jointTest S).high r) ψ‖ ≤ τ) :
    ApproxOn (act (reflectionMatrix R) ψ) ((ell : ℝ) + p.natDegree)
      ((9 : ℝ)^ell * weight N p)
      ((9 : ℝ)^ell * (δ + (1 + weight N p) * τ))
      (conjugate (reflectionMatrix R) D) := by
  let A := R.touching J
  have hlen : A.gates.length ≤ ell := (R.touching_length J).trans hJ
  have hξ : ‖act (reflectionMatrix R) ψ‖ ≤ 1 :=
    (act_unitary_norm (reflectionMatrix_unitary R) ψ).trans_le hψ
  have ht : ‖act ((jointTest A.gates).high r) (act (reflectionMatrix R) ψ)‖ ≤ τ := by
    exact (reflection_joint_tail_eq R A.gates (List.filter_sublist) r ψ).trans_le
      (htail A.gates (List.filter_sublist) hlen)
  have h := reflection_expansion_approximation hspec A.gates A.disjoint
    (act (reflectionMatrix R) ψ) hξ J D hD hDn p r δ τ hδ hp0 hp ht
  have hc : (9 : ℝ)^A.gates.length ≤ (9 : ℝ)^ell := pow_le_pow_right₀ (by norm_num) hlen
  have heq : conjugate (reflectionMatrix R) D = conjugate (reflectList A.gates) D := by
    calc
      _ = conjugate (reflectionMatrix A) D := R.touching_conjugate J D hD
      _ = _ := congrArg (fun U : Operator N => conjugate U D) (reflectionMatrix_eq A)
  have hcard : (J.card : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hJ
  have hdeg : (J.card : ℝ) + p.natDegree ≤ (ell : ℝ) + p.natDegree := by linarith
  have hnorm := mul_le_mul_of_nonneg_right hc (weight_nonneg (Nat.cast_nonneg N) p)
  have herror := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ δ + (1 + weight N p) * τ by
      have := weight_nonneg (Nat.cast_nonneg N) p
      positivity)
  exact (h.mono hdeg hnorm herror).congr_operator heq.symm

theorem low_degree_reflection_approximation
    (hpauli : PublishedPauliExpansion) (hspec : PublishedProductSpectralResolution)
    {N ell : ℕ} (hN : 1 ≤ N) (R : ReflectionLayer N) (ψ : State N) (hψ : ‖ψ‖ ≤ 1)
    (E : Operator N) (hE : HasDegreeLE E ell) (p : Polynomial ℝ)
    (r δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hp0 : p.eval 0 = 1)
    (hp : ∀ k : ℕ, 1 ≤ k → (k : ℝ) < r → |p.eval (k : ℝ)| ≤ δ)
    (htail : ∀ S : List (Count N), S.Sublist R.gates → S.length ≤ ell →
      ‖act ((jointTest S).high r) ψ‖ ≤ τ) :
    ApproxOn (act (reflectionMatrix R) ψ) ((ell : ℝ) + p.natDegree)
      (propagationBudget N ell * ‖E‖ * weight N p)
      (propagationBudget N ell * ‖E‖ * (δ + (1 + weight N p) * τ))
      (conjugate (reflectionMatrix R) E) := by
  let ξ := act (reflectionMatrix R) ψ
  let W := weight N p
  let ε := δ + (1 + W) * τ
  have hW : 0 ≤ W := weight_nonneg (Nat.cast_nonneg N) p
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  obtain ⟨terms, hsum, hsupp, hmass⟩ := hpauli N ell hN E hE
  have hterm : ∀ t ∈ terms,
      ApproxOn ξ ((ell : ℝ) + p.natDegree) ((9 : ℝ)^ell * W)
        ((9 : ℝ)^ell * ε) (conjugate (reflectionMatrix R) (localMatrix t.gates)) := by
    intro t ht
    have hn : ‖localMatrix t.gates‖ ≤ 1 :=
      (CStarRing.norm_coe_unitary (⟨localMatrix t.gates, localMatrix_unitary t.gates⟩ :
        unitary (Operator N))).le
    exact tensor_reflection_approximation hspec R ψ hψ t.support (hsupp t ht)
      (localMatrix t.gates) (localMatrix_supported t.gates t.support t.outside) hn
      p r δ τ hδ hτ hp0 hp htail
  have heq : conjugate (reflectionMatrix R) E =
      (terms.map (fun t => t.coeff • conjugate (reflectionMatrix R) (localMatrix t.gates))).sum := by
    rw [hsum]
    exact conjugate_complex_list_sum (reflectionMatrix R) terms
      LocalExpansionTerm.coeff (fun t => localMatrix t.gates)
  rw [heq]
  have hh := approx_list_sum ξ terms LocalExpansionTerm.coeff
    (fun t => conjugate (reflectionMatrix R) (localMatrix t.gates))
    ((ell : ℝ) + p.natDegree) ((9 : ℝ)^ell * W) ((9 : ℝ)^ell * ε) hterm
  apply hh.mono le_rfl
  · calc
      _ ≤ (((ell + 1 : ℕ) : ℝ) * (3 * N : ℝ)^ell * ‖E‖) * ((9 : ℝ)^ell * W) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = _ := by dsimp [propagationBudget, W]; ring
  · calc
      _ ≤ (((ell + 1 : ℕ) : ℝ) * (3 * N : ℝ)^ell * ‖E‖) * ((9 : ℝ)^ell * ε) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = _ := by dsimp [propagationBudget, ε, W]; ring

end QAC

end

end OAI
