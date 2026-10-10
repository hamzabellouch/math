import OAI.Probability.DilutedSpin.Core

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

/-- Product replacement on bounded spin coordinates, with its exact finite
sum of coordinate errors. -/
theorem bounded_product_difference {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i-g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hF := hf a (Finset.mem_insert_self a s)
    have hG : |∏ i ∈ s, g i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) hg'
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha]
    calc
      _ = |f a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))+(f a-g a)*(∏ i ∈ s, g i)| := by
        congr 1; ring
      _ ≤ |f a| * |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)|+|f a-g a| * |∏ i ∈ s, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))) ((f a-g a)*(∏ i ∈ s, g i))
      _ ≤ 1*(∑ i ∈ s, |f i-g i|)+|f a-g a| * 1 :=
        add_le_add (mul_le_mul hF (ih hf' hg') (abs_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hG (abs_nonneg _))
      _ = _ := by ring

theorem bounded_product_difference_sq {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    ((∏ i, f i)-(∏ i, g i))^2 ≤ (Fintype.card ι : ℝ)*∑ i, (f i-g i)^2 := by
  have hb := bounded_product_difference Finset.univ f g (fun i _ => hf i) (fun i _ => hg i)
  have hn : 0 ≤ ∑ i, |f i-g i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |f i-g i|)
  simp only [Finset.card_univ,sq_abs] at hs
  have hsq : ((∏ i, f i)-(∏ i, g i))^2 ≤ (∑ i, |f i-g i|)^2 := by
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hn] using hb)
  exact hsq.trans hs

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

/-- The one-vertex delay inequality decor:one-vertex-shift. The left side
compares independent child continuations with one shared extra transition. -/
theorem product_mean_shift_sq (P : FiniteLaw Ω) {ι : Type*} [Fintype ι]
    (f : ι → Ω → ℝ) (hf : ∀ i x, |f i x| ≤ 1) :
    ((∏ i, P.expect (f i))-P.expect (fun x => ∏ i, f i x))^2 ≤
      (Fintype.card ι : ℝ)*∑ i, P.covariance (f i) (f i) := by
  have hh := P.sq_expect_le_expect_sq (fun x => (∏ i, f i x)-(∏ i, P.expect (f i)))
  simp only [expect_sub,expect_const] at hh
  have hb := P.expect_mono (fun x => bounded_product_difference_sq
    (fun i => f i x) (fun i => P.expect (f i)) (fun i => hf i x)
    (fun i => P.abs_expect_le (hf i)))
  rw [expect_mul_left,expect_fintype_sum] at hb
  simp_rw [expect_sq_sub_expect] at hb
  simp only [covariance,pow_two] at hh hb ⊢
  nlinarith

end FiniteLaw
end DilutedSpinGlass

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Every descendant leaf receives the same one-site terminal observable,
with its own sampled path. -/
noncomputable def leafProduct : {n : ℕ} → (S : PrescribedTree n) →
    (FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0, .leaf, f, _ => f ()
  | _+1, .node _ C, f, z => ∏ i, leafProduct (C i) (fun y => f ((z i).1,y)) (z i).2

omit [Fintype Ω] in
theorem leafProduct_eq_prod {n : ℕ} (S : PrescribedTree n)
    (f : FinitePath Ω n → ℝ) (z : Sample Ω S) :
    leafProduct S f z = ∏ a : Leaf S, f (pathAt S a z) := by
  induction S with
  | leaf =>
    change f () = ∏ _ : Unit, f ()
    simp
  | @node n k C ih =>
    simp only [leafProduct]
    change _ = ∏ a : (i : Fin k) × Leaf (C i), f (pathAt (.node k C) a z)
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl (fun i _ => ih i (fun y => f ((z i).1,y)) (z i).2)

/-- Recursive conditional mean of a descendant spin product. -/
noncomputable def treeMean : {n : ℕ} → (S : PrescribedTree n) → KernelTower Ω n →
    (FinitePath Ω n → ℝ) → ℝ
  | 0, .leaf, _, f => f ()
  | _+1, .node _ C, T, f => ∏ i, T.1.expect (fun a => treeMean (C i) (T.2 a) (fun y => f (a,y)))

theorem treeMean_eq_expect {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (f : FinitePath Ω n → ℝ) : treeMean S T f = (sampleLaw S T).expect (leafProduct S f) := by
  induction S with
  | leaf =>
    change f () = KernelTower.unitLaw.expect (fun _ => f ())
    rw [FiniteLaw.expect_const]
  | @node n k C ih =>
    change FiniteLaw Ω × (Ω → KernelTower Ω n) at T
    rcases T with ⟨P,Q⟩
    change (Ω × FinitePath Ω n) → ℝ at f
    change (∏ i, P.expect (fun a => treeMean (C i) (Q a) (fun y => f (a,y)))) =
      (FiniteLaw.pi (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))).expect
        (fun z => ∏ i, leafProduct (C i) (fun y => f ((z i).1,y)) (z i).2)
    rw [FiniteLaw.expect_pi_product (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))
      (fun i (z : Ω × Sample Ω (C i)) => leafProduct (C i) (fun y => f (z.1,y)) z.2)]
    apply Finset.prod_congr rfl
    intro i _
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact ih i (Q a) (fun y => f (a,y))

omit [Fintype Ω] in
theorem leafProduct_bound {n : ℕ} (S : PrescribedTree n)
    {f : FinitePath Ω n → ℝ} (hf : ∀ x, |f x| ≤ 1) (z : Sample Ω S) :
    |leafProduct S f z| ≤ 1 := by
  rw [leafProduct_eq_prod,Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun a _ => hf (pathAt S a z))

theorem treeMean_bound {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    {f : FinitePath Ω n → ℝ} (hf : ∀ x, |f x| ≤ 1) : |treeMean S T f| ≤ 1 := by
  rw [treeMean_eq_expect]
  exact (sampleLaw S T).abs_expect_le (leafProduct_bound S hf)

/-- One literal unary stretch; it samples one transition from the original
kernel tower rather than introducing independent or replacement disorder. -/
def unary {n : ℕ} (S : PrescribedTree n) : PrescribedTree (n+1) := .node 1 (fun _ => S)

@[simp] theorem treeMean_unary {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω (n+1))
    (f : FinitePath Ω (n+1) → ℝ) : treeMean (unary S) T f =
      T.1.expect (fun a => treeMean S (T.2 a) (fun y => f (a,y))) := by
  change (∏ _ : Fin 1, T.1.expect (fun a => treeMean S (T.2 a) (fun y => f (a,y)))) = _
  simp

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Literal delay of a branching vertex. Every child loses one initial unary
transition; that transition is instead shared by all the children. Both terms
are expectations of the actual prescribed-tree products under the same tower. -/
theorem treeMean_one_vertex_shift {n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree n)
    (T : KernelTower Ω (n+2)) (f : FinitePath Ω (n+2) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    (treeMean (.node k (fun i => unary (C i))) T f-
      treeMean (unary (.node k C)) T f)^2 ≤
      (k : ℝ)*∑ i, T.1.covariance
        (fun a => treeMean (unary (C i)) (T.2 a) (fun y => f (a,y)))
        (fun a => treeMean (unary (C i)) (T.2 a) (fun y => f (a,y))) := by
  change FiniteLaw Ω × (Ω → KernelTower Ω (n+1)) at T
  rcases T with ⟨P,Q⟩
  change (Ω × FinitePath Ω (n+1)) → ℝ at f
  have h := P.product_mean_shift_sq
    (fun i a => treeMean (unary (C i)) (Q a) (fun y => f (a,y)))
    (fun i a => treeMean_bound (unary (C i)) (Q a) (fun y => hf (a,y)))
  simp only [Fintype.card_fin] at h
  convert h using 1
  congr 2
  change (∏ _ : Fin 1, P.expect (fun a => treeMean (.node k C) (Q a) (fun y => f (a,y)))) = _
  simp only [Fin.prod_univ_one]
  apply P.expect_congr
  intro a
  change (∏ i, (Q a).1.expect (fun b => treeMean (C i) ((Q a).2 b) (fun y => f (a,(b,y))))) = _
  simp only [treeMean_unary]

/-- Propagation to an ancestral branching vertex consists only of conditional
expectation and bounded products. This squared contraction estimate is
uniform in the transition probabilities and the number of sites. -/
theorem treeMean_node_difference_sq {n : ℕ} (k : ℕ+)
    (C D : Fin k → PrescribedTree n) (T : KernelTower Ω (n+1))
    (f : FinitePath Ω (n+1) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (treeMean (.node k C) T f-treeMean (.node k D) T f)^2 ≤
      (k : ℝ)*∑ i, T.1.expect (fun a =>
        (treeMean (C i) (T.2 a) (fun y => f (a,y))-
          treeMean (D i) (T.2 a) (fun y => f (a,y)))^2) := by
  change FiniteLaw Ω × (Ω → KernelTower Ω n) at T
  rcases T with ⟨P,Q⟩
  change (Ω × FinitePath Ω n) → ℝ at f
  have hc (i : Fin k) : |P.expect (fun a => treeMean (C i) (Q a) (fun y => f (a,y)))| ≤ 1 :=
    P.abs_expect_le (fun a => treeMean_bound (C i) (Q a) (fun y => hf (a,y)))
  have hd (i : Fin k) : |P.expect (fun a => treeMean (D i) (Q a) (fun y => f (a,y)))| ≤ 1 :=
    P.abs_expect_le (fun a => treeMean_bound (D i) (Q a) (fun y => hf (a,y)))
  have h := bounded_product_difference_sq
    (fun i => P.expect (fun a => treeMean (C i) (Q a) (fun y => f (a,y))))
    (fun i => P.expect (fun a => treeMean (D i) (Q a) (fun y => f (a,y)))) hc hd
  simp only [Fintype.card_fin] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_)) (Nat.cast_nonneg _))
  have hh := P.sq_expect_le_expect_sq (fun a =>
    treeMean (C i) (Q a) (fun y => f (a,y))-treeMean (D i) (Q a) (fun y => f (a,y)))
  rwa [FiniteLaw.expect_sub] at hh

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
