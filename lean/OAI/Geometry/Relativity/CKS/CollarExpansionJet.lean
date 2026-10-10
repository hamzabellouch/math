import OAI.Geometry.Relativity.CKS.MatrixScalarJets

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev ExpansionInput := MatrixScalarJet × (I → MatrixScalarJet) × MatrixScalarJet ×
  (I → ScalarJet) × (I → I → ScalarJet)

def normalizedLieJet (j : ExpansionInput) (i k : I) : ScalarJet := ∑ a,
  (productJet (j.2.2.2.1 a) (j.2.1 a i k)+
    productJet (j.1 a k) (j.2.2.2.2 i a)+productJet (j.1 i a) (j.2.2.2.2 k a))

def normalizedExpansionJet (j : ExpansionInput) : ScalarJet :=
  constantJet 1+(1/4:ℝ) • ∑ i, ∑ k,
    productJet (inverseMatrixJet j.1 i k) (j.2.2.1 k i-normalizedLieJet j k i)

def expansionRegion : Set ExpansionInput := {j | determinant (fun i k => (j.1 i k).1) ≠ 0}

def expansionReference (q : MatrixScalarJet) (dq : I → MatrixScalarJet) : ExpansionInput :=
  (q,dq,0,0,0)

lemma productJet_zero_right (f : ScalarJet) : productJet f 0 = 0 := by
  ext a b <;> simp [productJet]
lemma productJet_zero_left (f : ScalarJet) : productJet 0 f = 0 := by
  ext a b <;> simp [productJet]

lemma normalizedExpansion_reference (q : MatrixScalarJet) (dq : I → MatrixScalarJet) :
    normalizedExpansionJet (expansionReference q dq) = constantJet 1 := by
  simp [normalizedExpansionJet,normalizedLieJet,expansionReference,
    productJet_zero_left,productJet_zero_right]

lemma normalizedLieJet_smooth (i k : I) : ContDiff ℝ ∞ (fun j : ExpansionInput => normalizedLieJet j i k) := by
  unfold normalizedLieJet
  apply ContDiff.sum
  intro a ha
  exact ((productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞
      (fun j : ExpansionInput => (j.2.2.2.1 a,j.2.1 a i k)))).add
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞
      (fun j : ExpansionInput => (j.1 a k,j.2.2.2.2 i a))))).add
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞
      (fun j : ExpansionInput => (j.1 i a,j.2.2.2.2 k a))))

lemma normalizedExpansionJet_smooth {j : ExpansionInput} (hj : j ∈ expansionRegion) :
    ContDiffAt ℝ ∞ normalizedExpansionJet j := by
  have hs : ContDiffAt ℝ ∞ (fun j : ExpansionInput => ∑ i, ∑ k,
      productJet (inverseMatrixJet j.1 i k) (j.2.2.1 k i-normalizedLieJet j k i)) j := by
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro k hk
    exact productJet_smooth.contDiffAt.comp j
      (((inverseMatrixJet_smooth hj i k).comp j
        (by fun_prop : ContDiffAt ℝ ∞ (fun j : ExpansionInput => j.1) j)).prodMk
        ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ExpansionInput => j.2.2.1 k i) j).sub
          (normalizedLieJet_smooth k i).contDiffAt))
  exact contDiffAt_const.add (hs.const_smul (1/4:ℝ))

lemma expansionRegion_open : IsOpen expansionRegion := by
  exact isOpen_ne_fun ((determinant_smooth.continuous).comp (by fun_prop : Continuous (fun j : ExpansionInput => (fun i k => (j.1 i k).1)))) continuous_const

theorem expansion_uniform_lipschitz {K : Set ExpansionInput} (hK : IsCompact K)
    (hreg : K ⊆ expansionRegion) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
      LipschitzOnWith C normalizedExpansionJet (Metric.cthickening δ K) := by
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (I → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (I → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ (I → I → ScalarJet) := inferInstance
  let : ProperSpace ExpansionInput := FiniteDimensional.proper ℝ ExpansionInput
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open expansionRegion_open hreg
  refine ⟨δ,hδ,?_⟩
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hK.cthickening (r := δ))
  intro j hj
  obtain ⟨C,t,ht,hC⟩ := ((normalizedExpansionJet_smooth (hsub hj)).of_le
    (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
  exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩

def actualExpansionInput (q Q : Point → Mat) (S : Point → Point) (x : Point) : ExpansionInput :=
  (matrixScalarJets q x,
    (fun a => matrixScalarJets (fun y i k => D (basis a) (fun z => q z i k) y) x),
    matrixScalarJets Q x,
    (fun a => actualScalarJet (fun y => S y a) x),
    fun a b => actualScalarJet (D (basis a) (fun y => S y b)) x)

def normalizedLie (q : Point → Mat) (S : Point → Point) (x : Point) (i k : I) : ℝ := ∑ a,
  (S x a*D (basis a) (fun y => q y i k) x+
    q x a k*D (basis i) (fun y => S y a) x+q x i a*D (basis k) (fun y => S y a) x)

def normalizedExpansion (q Q : Point → Mat) (S : Point → Point) (x : Point) : ℝ :=
  1+(1/4:ℝ)*∑ i, ∑ k, inverse (q x) i k*(Q x k i-normalizedLie q S x k i)

lemma component_three {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 3 q x) (i k : I) :
    ContDiffAt ℝ 3 (fun y => q y i k) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

lemma normalizedLie_diff {q : Point → Mat} {S : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : I) :
    ContDiffAt ℝ 2 (fun y => normalizedLie q S y i k) x := by
  have hSa (a : I) := contDiffAt_pi.mp hS a
  have hqa := component_three hq
  have h23 : (2:ℕ∞ω) ≤ 3 := by norm_num
  apply ContDiffAt.sum
  intro a ha
  exact ((((hSa a).of_le h23).mul (contDiffAt_D (hqa i k) (by norm_num) (basis a))).add
      (((hqa a k).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis i)))).add
      (((hqa i a).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis k)))

lemma actual_normalizedLieJet {q Q : Point → Mat} {S : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : I) :
    actualScalarJet (fun y => normalizedLie q S y i k) x =
      normalizedLieJet (actualExpansionInput q Q S x) i k := by
  have hSa (a : I) := contDiffAt_pi.mp hS a
  have hqa := component_three hq
  have h23 : (2:ℕ∞ω) ≤ 3 := by norm_num
  have hdS (a b : I) : ContDiffAt ℝ 2 (D (basis a) (fun y => S y b)) x :=
    contDiffAt_D (hSa b) (by norm_num) (basis a)
  have hdq (a i k : I) : ContDiffAt ℝ 2 (D (basis a) (fun y => q y i k)) x :=
    contDiffAt_D (hqa i k) (by norm_num) (basis a)
  have hterm (a : I) : ContDiffAt ℝ 2 (fun y =>
      S y a*D (basis a) (fun z => q z i k) y+
      q y a k*D (basis i) (fun z => S z a) y+q y i a*D (basis k) (fun z => S z a) y) x :=
    ((((hSa a).of_le h23).mul (hdq a i k)).add
      (((hqa a k).of_le h23).mul (hdS i a))).add
      (((hqa i a).of_le h23).mul (hdS k a))
  unfold normalizedLie normalizedLieJet
  rw [actualScalarJet_sum _ (fun a _ => hterm a)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [actualScalarJet_add ((((hSa a).of_le h23).mul (hdq a i k)).add
      (((hqa a k).of_le h23).mul (hdS i a))) (((hqa i a).of_le h23).mul (hdS k a)),
    actualScalarJet_add (((hSa a).of_le h23).mul (hdq a i k)) (((hqa a k).of_le h23).mul (hdS i a)),
    actualScalarJet_mul ((hSa a).of_le h23) (hdq a i k),
    actualScalarJet_mul ((hqa a k).of_le h23) (hdS i a),
    actualScalarJet_mul ((hqa i a).of_le h23) (hdS k a)]
  rfl

theorem actual_normalizedExpansionJet {q Q : Point → Mat} {S : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hQ : ContDiffAt ℝ 2 Q x) (hS : ContDiffAt ℝ 3 S x)
    (h0 : determinant (q x) ≠ 0) :
    actualScalarJet (normalizedExpansion q Q S) x =
      normalizedExpansionJet (actualExpansionInput q Q S x) := by
  have hq2 : ContDiffAt ℝ 2 q x := hq.of_le (by norm_num)
  have hi (i k : I) : ContDiffAt ℝ 2 (fun y => inverse (q y) i k) x := by
    unfold inverse
    apply ContDiffAt.div
    · fin_cases i <;> fin_cases k <;> dsimp <;>
        first | exact component_diff hq2 _ _ | exact (component_diff hq2 _ _).neg
    · exact (determinant_smooth.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq2
    · exact h0
  have hs (i k : I) : ContDiffAt ℝ 2 (fun y => Q y k i-normalizedLie q S y k i) x :=
    (component_diff hQ k i).sub (normalizedLie_diff hq hS k i)
  have ht (i k : I) := (hi i k).mul (hs i k)
  have hsum : ContDiffAt ℝ 2 (fun y => ∑ i, ∑ k,
      inverse (q y) i k*(Q y k i-normalizedLie q S y k i)) x :=
    ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ht i k))
  unfold normalizedExpansion normalizedExpansionJet
  change actualScalarJet (fun y => 1 + (1/4:ℝ) • (∑ i, ∑ k,
    inverse (q y) i k*(Q y k i-normalizedLie q S y k i))) x = _
  rw [actualScalarJet_add contDiffAt_const (hsum.const_smul (1/4:ℝ)),
    actualScalarJet_const]
  simp only [smul_eq_mul]
  rw [actualScalarJet_smul (1/4:ℝ) hsum,
    actualScalarJet_sum _ (fun i _ => ContDiffAt.sum (fun k _ => ht i k))]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi'
  rw [actualScalarJet_sum _ (fun k _ => ht i k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [actualScalarJet_mul (hi i k) (hs i k),
    actual_inverseMatrixJet hq2 h0 i k,
    actualScalarJet_sub (component_diff hQ k i) (normalizedLie_diff hq hS k i),
    actual_normalizedLieJet hq hS]
  rfl

end
end CKSAngularGeometry

end

end OAI
