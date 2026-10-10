import OAI.Analysis.KadisonSimilarity.Tensor.EndpointDensity
import OAI.Analysis.KadisonSimilarity.Tensor.MultiplicityClassification

namespace OAI

/-! Dense elementary tensor tests for bounded maps on regrouped word spaces. -/

noncomputable section
namespace KadisonSimilarity
open scoped TensorProduct

section TensorPackets

variable {X B E F K : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- Hilbert tensor totality needs only a normed codomain. -/
theorem continuousLinearMap_ext_hilbertTensorInsert_normed
    (f g : HilbertTensor X B →L[ℂ] K)
    (h : ∀ a b, f (hilbertTensorInsert a b) = g (hilbertTensorInsert a b)) : f = g := by
  unfold HilbertTensor at *
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq f.continuous g.continuous
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul a b => exact h a b
    | add a b ha hb =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) ha hb

theorem continuous_hilbertTensorPair :
    Continuous (fun p : X × B => hilbertTensorInsert p.1 p.2) := by
  exact (UniformSpace.Completion.continuous_coe
    (α := X ⊗[ℂ] B)).comp TensorProduct.continuous_tmul

/-- One completed multiplicity word and one completed endpoint word. -/
def tensorPacket {n : ℕ} (p : ((Fin n → X) × B) × (E × (Fin n → F))) :
    HilbertTensor (HilbertTensor (CompletedTensorWord X n) B) (EndpointTensor E F n) :=
  hilbertTensorInsert (hilbertTensorInsert (completedTensorWord p.1.1) p.1.2)
    (endpointWord p.2.1 p.2.2)

/-- Completed word packets span their full Hilbert tensor space. -/
theorem continuousLinearMap_ext_tensorPackets {n : ℕ}
    (f g : HilbertTensor (HilbertTensor (CompletedTensorWord X n) B)
      (EndpointTensor E F n) →L[ℂ] K)
    (h : ∀ p, f (tensorPacket p) = g (tensorPacket p)) : f = g := by
  have he (a : Fin n → X) (b : B) :
      f.comp (hilbertTensorInsert (hilbertTensorInsert (completedTensorWord a) b)) =
        g.comp (hilbertTensorInsert (hilbertTensorInsert (completedTensorWord a) b)) := by
    apply continuousLinearMap_ext_endpointWords
    intro d c
    exact h ((a, b), (d, c))
  apply continuousLinearMap_ext_hilbertTensorInsert_normed
  intro j e
  have hj : f.comp (hilbertTensorRightInsert e) = g.comp (hilbertTensorRightInsert e) := by
    apply continuousLinearMap_ext_hilbertTensorInsert_normed
    intro a b
    have ha : (f.comp (hilbertTensorRightInsert e)).comp (hilbertTensorRightInsert b) =
        (g.comp (hilbertTensorRightInsert e)).comp (hilbertTensorRightInsert b) := by
      apply continuousLinearMap_ext_completedTensorWords
      intro c
      exact congrArg (fun z : EndpointTensor E F n →L[ℂ] K => z e) (he c b)
    exact congrArg (fun z : CompletedTensorWord X n →L[ℂ] K => z a) ha
  exact congrArg (fun z : HilbertTensor (CompletedTensorWord X n) B →L[ℂ] K => z j) hj

/-- Dense alphabet vectors determine a map on completed tensor words. -/
theorem continuousLinearMap_ext_denseCompletedWords {DX : Type*} (vx : DX → X)
    (hx : DenseRange vx) {n : ℕ} (f g : CompletedTensorWord X n →L[ℂ] K)
    (h : ∀ a : Fin n → DX, f (completedTensorWord (fun i => vx (a i))) =
      g (completedTensorWord (fun i => vx (a i)))) : f = g := by
  have hd := DenseRange.piMap (fun _ : Fin n => hx)
  have heq := hd.equalizer (f.continuous.comp (continuous_completedTensorWord n))
    (g.continuous.comp (continuous_completedTensorWord n)) (funext h)
  apply continuousLinearMap_ext_completedTensorWords
  intro a
  exact congrFun heq a

/-- Dense base vectors and centered alphabets determine multiplicity maps. -/
theorem continuousLinearMap_ext_denseMultiplicityWords {DX DB : Type*}
    (vx : DX → X) (vb : DB → B) (hx : DenseRange vx) (hb : DenseRange vb) {n : ℕ}
    (f g : HilbertTensor (CompletedTensorWord X n) B →L[ℂ] K)
    (h : ∀ (a : Fin n → DX) (b : DB),
      f (hilbertTensorInsert (completedTensorWord (fun i => vx (a i))) (vb b)) =
      g (hilbertTensorInsert (completedTensorWord (fun i => vx (a i))) (vb b))) : f = g := by
  have ha (a : Fin n → DX) :
      f.comp (hilbertTensorInsert (completedTensorWord (fun i => vx (a i)))) =
        g.comp (hilbertTensorInsert (completedTensorWord (fun i => vx (a i)))) := by
    apply DFunLike.coe_injective
    exact hb.equalizer (by fun_prop) (by fun_prop) (funext (h a))
  apply continuousLinearMap_ext_hilbertTensorInsert_normed
  intro x b
  have heq : f.comp (hilbertTensorRightInsert b) = g.comp (hilbertTensorRightInsert b) := by
    apply continuousLinearMap_ext_denseCompletedWords vx hx
    intro a
    exact congrArg (fun L : B →L[ℂ] K => L b) (ha a)
  exact congrArg (fun L : CompletedTensorWord X n →L[ℂ] K => L x) heq

/-- Dense endpoint vectors and centered alphabets determine endpoint maps. -/
theorem continuousLinearMap_ext_denseEndpointWords {DE DF : Type*}
    (ve : DE → E) (vf : DF → F) (he : DenseRange ve) (hf : DenseRange vf) {n : ℕ}
    (f g : EndpointTensor E F n →L[ℂ] K)
    (h : ∀ (d : DE) (c : Fin n → DF),
      f (endpointWord (ve d) (fun i => vf (c i))) =
        g (endpointWord (ve d) (fun i => vf (c i)))) : f = g := by
  have hd (d : DE) : f.comp (endpointInsert (ve d)) = g.comp (endpointInsert (ve d)) := by
    apply continuousLinearMap_ext_denseCompletedWords vf hf
    intro c
    exact h d c
  apply continuousLinearMap_ext_endpointWords
  intro d c
  have heq : f.comp (hilbertTensorRightInsert (completedTensorWord c)) =
      g.comp (hilbertTensorRightInsert (completedTensorWord c)) := by
    apply DFunLike.coe_injective
    apply he.equalizer (by fun_prop) (by fun_prop)
    funext e
    exact congrArg (fun L : CompletedTensorWord F n →L[ℂ] K => L (completedTensorWord c)) (hd e)
  exact congrArg (fun L : E →L[ℂ] K => L d) heq

/-- Dense choices for each algebra letter suffice in the packet test. -/
theorem continuousLinearMap_ext_denseTensorPackets
    {DX DB DE DF : Type*} (vx : DX → X) (vb : DB → B) (ve : DE → E) (vf : DF → F)
    (hx : DenseRange vx) (hb : DenseRange vb) (he : DenseRange ve) (hf : DenseRange vf)
    {n : ℕ} (f g : HilbertTensor (HilbertTensor (CompletedTensorWord X n) B)
      (EndpointTensor E F n) →L[ℂ] K)
    (h : ∀ (a : Fin n → DX) (b : DB) (d : DE) (c : Fin n → DF),
      f (tensorPacket ((fun i => vx (a i), vb b), (ve d, fun i => vf (c i)))) =
        g (tensorPacket ((fun i => vx (a i), vb b), (ve d, fun i => vf (c i))))) : f = g := by
  have ha (a : Fin n → DX) (b : DB) :
      f.comp (hilbertTensorInsert (hilbertTensorInsert (completedTensorWord (fun i => vx (a i))) (vb b))) =
        g.comp (hilbertTensorInsert (hilbertTensorInsert (completedTensorWord (fun i => vx (a i))) (vb b))) := by
    apply continuousLinearMap_ext_denseEndpointWords ve vf he hf
    exact h a b
  apply continuousLinearMap_ext_hilbertTensorInsert_normed
  intro j e
  have hj : f.comp (hilbertTensorRightInsert e) = g.comp (hilbertTensorRightInsert e) := by
    apply continuousLinearMap_ext_denseMultiplicityWords vx vb hx hb
    intro a b
    exact congrArg (fun L : EndpointTensor E F n →L[ℂ] K => L e) (ha a b)
  exact congrArg (fun L : HilbertTensor (CompletedTensorWord X n) B →L[ℂ] K => L j) hj

/-- A function-level form avoids comparing bundled maps across independently
synthesized completed-tensor instances. -/
theorem function_ext_denseTensorPackets
    {DX DB DE DF : Type*} (vx : DX → X) (vb : DB → B) (ve : DE → E) (vf : DF → F)
    (hx : DenseRange vx) (hb : DenseRange vb) (he : DenseRange ve) (hf : DenseRange vf)
    {n : ℕ}
    (p q : HilbertTensor (HilbertTensor (CompletedTensorWord X n) B) (EndpointTensor E F n) → K)
    (hp : Continuous p) (hq : Continuous q)
    (hpadd : ∀ x y, p (x + y) = p x + p y) (hqadd : ∀ x y, q (x + y) = q x + q y)
    (hpsmul : ∀ (c : ℂ) x, p (c • x) = c • p x)
    (hqsmul : ∀ (c : ℂ) x, q (c • x) = c • q x)
    (h : ∀ (a : Fin n → DX) (b : DB) (d : DE) (c : Fin n → DF),
      p (tensorPacket ((fun i => vx (a i), vb b), (ve d, fun i => vf (c i)))) =
        q (tensorPacket ((fun i => vx (a i), vb b), (ve d, fun i => vf (c i))))) : p = q := by
  let fp : HilbertTensor (HilbertTensor (CompletedTensorWord X n) B)
      (EndpointTensor E F n) →L[ℂ] K :=
    { toFun := p
      map_add' := hpadd
      map_smul' := hpsmul
      cont := hp }
  let fq : HilbertTensor (HilbertTensor (CompletedTensorWord X n) B)
      (EndpointTensor E F n) →L[ℂ] K :=
    { toFun := q
      map_add' := hqadd
      map_smul' := hqsmul
      cont := hq }
  have heq := continuousLinearMap_ext_denseTensorPackets vx vb ve vf hx hb he hf fp fq h
  exact congrArg (fun L : HilbertTensor (HilbertTensor (CompletedTensorWord X n) B)
    (EndpointTensor E F n) →L[ℂ] K => (L : _ → K)) heq

end TensorPackets

end KadisonSimilarity

end

end OAI
