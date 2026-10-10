import OAI.Probability.DilutedSpin.GlobalSelectedAverage
import OAI.Probability.DilutedSpin.HistoryRetained
import OAI.Probability.DilutedSpin.MatrixNormalization
import OAI.Probability.DilutedSpin.PairSquare
import OAI.Probability.DilutedSpin.TreeMeasurable

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance matrixPairPropDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {n : ℕ}

omit [Fintype C] [DecidableEq C] in
lemma singleton_history_cover (S : PrescribedTree n) (x : S.Leaf) (a : C) :
    HistoryCover S (Finset.univ.erase x) id ({a} : Finset C) (fun _ => x) := by
  classical
  refine ⟨⟨Function.injective_id,?_,?_⟩,?_⟩
  · intro c hc d hd _
    simp only [Finset.mem_coe,Finset.mem_singleton] at hc hd
    exact hc.trans hd.symm
  · intro y hy c _
    exact (Finset.mem_erase.mp hy).1
  · intro y
    by_cases h : y = x
    · exact Or.inr ⟨a,by simp,h⟩
    · exact Or.inl ⟨y,by simp [h],rfl⟩

/-- The actual full prescribed split-matrix history, retaining just the anchor
and the first newly assigned path, is its exact kappa ratio times the literal
one-color pair history. All unused old replicas and their joint test remain.
This is not a reference-history assumption. -/
theorem matrixHistory_first_pair (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (x : S.Leaf)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect
        (fun z => g z * R (D.pathAt (pos a) z) (D.pathAt (pos c) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f =
    (partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)) *
      pairObservableHistory K m S x (splitDepth T (q a) (q c)) R f := by
  classical
  let P : Finset C := {a}
  have hc : c ∉ P := by simpa only [P,Finset.mem_singleton] using hac.symm
  have hcover := singleton_history_cover S x a
  have hsplit : ∀ b ∈ P, ∀ d ∈ P,
      splitDepth S ((fun _ : C => x) b) ((fun _ : C => x) d) = splitDepth T (q b) (q d) := by
    intro b hb d hd
    have hb' : b = a := Finset.mem_singleton.mp hb
    have hd' : d = a := Finset.mem_singleton.mp hd
    subst b; subst d
    simp only [splitDepth_self]
  let G : (C → FinitePath Ω n) → ℝ := fun y => R (y a) (y c)
  have hG : ∀ y z, (∀ b ∈ insert c P, y b = z b) → G y = G z := by
    intro y z h
    dsimp only [G]
    rw [h a (by simp [P]),h c (by simp)]
  let A := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c P).image q)
  let V := fun (D : PrescribedTree n) (pos : C → D.Leaf) (g : Sample Ω D → ℝ) =>
    (D.sampleLaw K).expect (fun z => g z * R (D.pathAt (pos a) z) (D.pathAt (pos c) z))
  have old (y : S.Leaf) (hy : y ∈ Finset.univ.erase x)
      (hs : splitDepth S x y = splitDepth T (q a) (q c)) :
      weightedMatrixHistory T q V m cs S ((Finset.univ.erase x).erase y) id
        (Function.update (fun _ => x) c y) f =
      A * (S.sampleLaw K).expect (fun z => f z * R (S.pathAt x z) (S.pathAt y z)) := by
    have hs' : ∀ b ∈ P, splitDepth S (id y) ((fun _ : C => x) b) = splitDepth T (q c) (q b) := by
      intro b hb
      have hb' : b = a := Finset.mem_singleton.mp hb
      subst b
      simpa only [id_eq,splitDepth_symm S y x,splitDepth_symm T (q c) (q a)] using hs
    have h := matrixHistory_retained T q hq K m hm hp hend cs hcs (insert c P)
      (Finset.insert_nonempty _ _) hdis hfull G hG S ((Finset.univ.erase x).erase y) id _
      (hcover.pick_old hc hy) (splitOn_pick_old T S q P c hc _ y hsplit hs') f
    simpa only [weightedMatrixHistory,V,G,A,id_eq,Function.update_self,Function.update_of_ne hac] using h
  have fresh (v : S.Internal)
      (hs : splitDepth (grow S v) (oldLeaf S v x) (newLeaf S v) = splitDepth T (q a) (q c)) :
      weightedMatrixHistory T q V m cs (grow S v) (Finset.univ.erase x)
        (fun y => oldLeaf S v (id y))
        (Function.update (fun _ => oldLeaf S v x) c (newLeaf S v))
        (fun z => f (oldSample S v z)) =
      A * ((grow S v).sampleLaw K).expect (fun z => f (oldSample S v z) *
        R ((grow S v).pathAt (oldLeaf S v x) z) ((grow S v).pathAt (newLeaf S v) z)) := by
    have hs' : ∀ b ∈ P, freshSplitDepth S v ((fun _ : C => x) b) = splitDepth T (q c) (q b) := by
      intro b hb
      have hb' : b = a := Finset.mem_singleton.mp hb
      subst b
      simpa only [splitDepth_symm (grow S v) (oldLeaf S v x),splitDepth_new_old,
        splitDepth_symm T (q a) (q c)] using hs
    have h := matrixHistory_retained T q hq K m hm hp hend cs hcs (insert c P)
      (Finset.insert_nonempty _ _) hdis hfull G hG (grow S v) (Finset.univ.erase x) _ _
      (hcover.pick_fresh hc v) (splitOn_pick_fresh T S q P c hc _ v hsplit hs')
      (fun z => f (oldSample S v z))
    simpa only [weightedMatrixHistory,V,G,A,id_eq,Function.update_self,Function.update_of_ne hac] using h
  change weightedMatrixHistory T q V m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f = _
  rw [weightedMatrixHistory_step T q V m c cs P hc hdis]
  have ho (y : S.Leaf) (hy : y ∈ Finset.univ.erase x) :
      (if ∀ d ∈ P, splitDepth S (id y) ((fun _ : C => x) d) = splitDepth T (q c) (q d)
        then weightedMatrixHistory T q V m cs S ((Finset.univ.erase x).erase y) id
          (Function.update (fun _ => x) c (id y)) f else 0) =
      A * (if splitDepth S x y = splitDepth T (q a) (q c)
        then (S.sampleLaw K).expect (fun z => f z * R (S.pathAt x z) (S.pathAt y z)) else 0) := by
    have he : (∀ d ∈ P, splitDepth S (id y) ((fun _ : C => x) d) = splitDepth T (q c) (q d)) ↔
        splitDepth S x y = splitDepth T (q a) (q c) := by
      simp only [P,Finset.mem_singleton,forall_eq,id_eq,splitDepth_symm S y x,splitDepth_symm T (q c) (q a)]
    simp only [he]
    split_ifs with hs
    · exact old y hy hs
    · exact (mul_zero A).symm
  have hv (v : S.Internal) :
      (if ∀ d ∈ P, freshSplitDepth S v ((fun _ : C => x) d) = splitDepth T (q c) (q d)
        then gamma S m v * weightedMatrixHistory T q V m cs (grow S v) (Finset.univ.erase x)
          (fun y => oldLeaf S v (id y))
          (Function.update (fun _ => oldLeaf S v x) c (newLeaf S v))
          (fun z => f (oldSample S v z)) else 0) =
      A * (if splitDepth (grow S v) (oldLeaf S v x) (newLeaf S v) = splitDepth T (q a) (q c)
        then gamma S m v * ((grow S v).sampleLaw K).expect (fun z => f (oldSample S v z) *
          R ((grow S v).pathAt (oldLeaf S v x) z) ((grow S v).pathAt (newLeaf S v) z)) else 0) := by
    have he : (∀ d ∈ P, freshSplitDepth S v ((fun _ : C => x) d) = splitDepth T (q c) (q d)) ↔
        splitDepth (grow S v) (oldLeaf S v x) (newLeaf S v) = splitDepth T (q a) (q c) := by
      simp only [P,Finset.mem_singleton,forall_eq,splitDepth_symm (grow S v) (oldLeaf S v x),
        splitDepth_new_old,splitDepth_symm T (q a) (q c)]
    simp only [he]
    split_ifs with hs
    · rw [fresh v hs]; ring
    · exact (mul_zero A).symm
  have he := Finset.sum_congr rfl ho
  rw [he]
  simp_rw [hv]
  rw [← Finset.mul_sum,← Finset.mul_sum,← mul_add]
  rfl

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
noncomputable local instance matrixPairRegularityPropDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n : ℕ}

lemma measurable_pairObservableHistory_tilt
    (T : KernelTower Ω n) (m : Fin n → ℝ) (exponents : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    {g : Z → FinitePath Ω n → ℝ}
    {R : Z → FinitePath Ω n → FinitePath Ω n → ℝ} {f : Z → Sample Ω S → ℝ}
    (hg : ∀ x, Measurable (fun z => g z x)) (hR : ∀ x y, Measurable (fun z => R z x y))
    (hf : ∀ x, Measurable (fun z => f z x)) :
    Measurable (fun z => pairObservableHistory (KernelTower.tilt n T m (g z)) exponents S a d (R z) (f z)) := by
  unfold pairObservableHistory
  apply Measurable.add
  · apply Finset.measurable_sum; intro b _
    split_ifs
    · exact measurable_tilt_sample_expect S T m hg (fun x => (hf x).mul (hR _ _))
    · exact measurable_const
  · apply Finset.measurable_sum; intro v _
    split_ifs
    · exact (measurable_tilt_sample_expect (grow S v) T m hg
        (fun x => (hf _).mul (hR _ _))).const_mul _
    · exact measurable_const

/-- Total absolute mass controlling one added color, with the entire old tree
left present. The bound is independent of the realized reservoir size. -/
noncomputable def pairHistoryMass (S : PrescribedTree n) (m : Fin (n+1) → ℝ) (a : S.Leaf) : ℝ :=
  ((Finset.univ : Finset S.Leaf).erase a).card + ∑ v : S.Internal, |gamma S m v|

lemma pairObservableHistory_bound (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ x y, |R x y| ≤ 1) (hf : ∀ x, |f x| ≤ B) :
    |pairObservableHistory T m S a d R f| ≤ pairHistoryMass S m a*B := by
  have hp (x : Sample Ω S) (y z) : |f x*R y z| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (hf x) (hR y z) (abs_nonneg _) hB).trans_eq (mul_one B)
  unfold pairObservableHistory pairHistoryMass
  calc
    _ ≤ (∑ b ∈ (Finset.univ : Finset S.Leaf).erase a,
      |if splitDepth S a b = d then (S.sampleLaw T).expect (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) else 0|) +
      ∑ v : S.Internal, |if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw T).expect (fun x => f (oldSample S v x)*
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (∑ _b ∈ (Finset.univ : Finset S.Leaf).erase a, B) + ∑ v : S.Internal, |gamma S m v| *B := by
      apply add_le_add
      · apply Finset.sum_le_sum; intro b _
        split_ifs
        · exact FiniteLaw.abs_expect_le _ (fun x => hp x _ _)
        · simpa using hB
      · apply Finset.sum_le_sum; intro v _
        split_ifs
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (FiniteLaw.abs_expect_le _ (fun x => hp _ _ _)) (abs_nonneg _)
        · simpa using mul_nonneg (abs_nonneg (gamma S m v)) hB
    _ = _ := by simp [← Finset.sum_mul,add_mul]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
