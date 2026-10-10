import OAI.Probability.DilutedSpin.UpperDatumIntegral

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [NeZero N] in
lemma realCountEnergy_succ (V : FinitePath Ω n → Fin N → Spin) (k : ℕ)
    (i : RootPath (Fin p → Fin N) k) (z : RootPath (InteractionSample p) k)
    (a : Fin p → Fin N) (θ : InteractionSample p) (f : FinitePath Ω n → ℝ) :
    realCountEnergy V (k+1) (a,i) (θ,z) f =
      realCountEnergy V k i z f+(fun y => θ.1 (fun j => V y (a j))) := by
  funext y
  simp only [realCountEnergy,Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ,Pi.add_apply]
  ring

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_real_succ (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    (a : UpperDatum p N R) :
    datumRoot T U V x m j f (k+1) l (a,z) w =
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l w)) m
        (fun y => cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
          (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
          (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f) y+
            a.1.1 (fun d => V (pathMap (cavityProject l) n y) (a.2.1 d))) := by
  unfold datumRoot
  simp only [rootMap,realCountEnergy_succ,cavityRoot]
  congr 1
  funext y
  exact cavityEnergy_add V x j l _ _ _ _ _ y

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_head_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    (a : UpperDatum p N R) {B C : ℝ} (hf : ∀ y,|f y|≤B)
    (hz : ∀ i,‖(rootArray k z i).1.1‖≤C) (hw : ∀ i,‖(rootArray l w i).1.1‖≤C)
    (ha : ‖a.1.1‖≤C) :
    |datumRoot T U V x m j f (k+1) l (a,z) w|≤B+C*(k+l+1) ∧
    |datumRoot T U V x m j f k (l+1) z (a,w)|≤B+C*(k+l+1) := by
  have hza : ∀ i : Fin (k+1),‖(rootArray (k+1) (a,z) i).1.1‖≤C :=
    fun i => Fin.cases ha hz i
  have hwa : ∀ i : Fin (l+1),‖(rootArray (l+1) (a,w) i).1.1‖≤C :=
    fun i => Fin.cases ha hw i
  constructor
  · convert datumRoot_bound T U V x m hm j f (k+1) l (a,z) w hf hza hw using 1
    push_cast
    ring
  · convert datumRoot_bound T U V x m hm j f k (l+1) z (a,w) hf hz hwa using 1
    push_cast
    ring


end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

noncomputable def freshRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool)
    (a : UpperDatum p N R) : ℝ :=
  backwardLog n (KernelTower.prod n T (piTower n (fun d => U (a.2.2 d)))) m
    (fun y => f (pathFst n y)+mixedTreeEnergy a.1 sel V x a.2.2 a.2.1 y)

omit [NeZero N] in
lemma measurable_freshRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool) :
    Measurable (freshRoot T U V x m f sel) := by
  apply measurable_from_prod_countable_left
  intro b
  unfold freshRoot
  dsimp only
  apply KernelTower.measurable_backwardLog
  intro y
  exact measurable_const.add (measurable_mixedEnergy _ _ _)

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma freshRoot_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool)
    (a : UpperDatum p N R) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |freshRoot T U V x m f sel a|≤B+‖a.1.1‖ := by
  apply backwardLog_bound n _ m hm
  intro y
  exact abs_add_le _ _ |>.trans (add_le_add (hf _) (mixedEnergy_bound a.1 sel _ _))

lemma freshRoot_mean_sub (M : Model p) (Q : FiniteLaw R) (T : KernelTower Ω n)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin (n+1) → ℝ) (hm : ∀ d : Fin n,0 < m d.succ)
    (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool) {B C : ℝ}
    (hf : ∀ y,|f y|≤B) (hC : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C) :
    (∫ a,freshRoot T U V x (fun d => m d.succ) f sel a ∂upperDatumLaw M Q)-
      backwardLog n T (fun d => m d.succ) f =
      ∫ θ,mixedRootIncrement T Q U V x m f θ sel ∂M.disorder.toMeasure := by
  let g := freshRoot T U V x (fun d => m d.succ) f sel
  have hg := measurable_freshRoot T U V x (fun d => m d.succ) f sel
  have hb : ∀ᵐ a ∂M.disorder.toMeasure,∀ i r,|g (a,i,r)|≤B+C := by
    filter_upwards [hC] with a ha
    intro i r
    exact (freshRoot_bound T U V x _ hm f sel (a,i,r) hf).trans (by linarith)
  rw [integral_upperDatumLaw M Q g hg hb]
  let G := fun θ => (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
    (fun i => (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r => g (θ,i,r)))
  have hG : Measurable G := FiniteLaw.measurable_expect _ (fun i =>
    FiniteLaw.measurable_expect _ (fun r => hg.comp (measurable_id.prodMk measurable_const)))
  have hiG : Integrable G M.disorder.toMeasure := by
    apply Integrable.of_bound hG.aestronglyMeasurable (B+C)
    filter_upwards [hb] with a ha
    exact FiniteLaw.abs_expect_le _ (fun i => FiniteLaw.abs_expect_le _ (ha i))
  change (∫ θ,G θ ∂M.disorder.toMeasure)-_=_
  have hc : backwardLog n T (fun d => m d.succ) f =
      ∫ _θ : InteractionSample p, backwardLog n T (fun d => m d.succ) f ∂M.disorder.toMeasure := by simp
  rw [hc] at ⊢
  rw [← integral_sub hiG (integrable_const _)]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [mixedRootIncrement,FiniteLaw.expect_sub,FiniteLaw.expect_const]
  rfl

lemma freshRoot_replacement (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (f : FinitePath Ω n → ℝ) (j : Fin p) {B C : ℝ}
    (hf : ∀ y,|f y|≤B) (hC : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C) :
    (∫ a,freshRoot T U V x (fun d => m d.succ) f (fun _ => true) a ∂upperDatumLaw M Q)+
      ((p-1:ℕ):ℝ)*backwardLog n T (fun d => m d.succ) f ≤
      (p:ℝ)*(∫ a,freshRoot T U V x (fun d => m d.succ) f (fun d => decide (d=j)) a ∂upperDatumLaw M Q)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  have h := integral_mixedRoot_combination_nonpos M hM T Q U V x m hm hpos hstrict hroot hend f j
  simp_rw [mixedRootIncrement_false] at h
  rw [← freshRoot_mean_sub M Q T U V x m hstrict f (fun _ => true) hf hC,
    ← freshRoot_mean_sub M Q T U V x m hstrict f (fun d => decide (d=j)) hf hC] at h
  have hp : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by have := hM.arity; omega : 1≤p),Nat.cast_one]
  rw [hp] at h ⊢
  nlinarith

end DilutedSpinGlass.PrescribedTree

end

end OAI
