import OAI.Analysis.AncientFlat.Regularity.InitialJetModel
import OAI.Analysis.AncientFlat.Evolution.TimePaste

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicInitial
open ParabolicInterior ParabolicSchauder ParametrixEvolution ClassicalIBP
variable {V : Type} [NormedAddCommGroup V]
def reflectTime (p : V × ℝ) : V × ℝ := (p.1,-p.2)
lemma pdist_reflect (p q : V × ℝ) : pdist (reflectTime p) (reflectTime q)=pdist p q := by
  simp only [pdist,reflectTime,neg_sub_neg,abs_sub_comm]
lemma holder_reflect {E : Type*} [NormedAddCommGroup E] {α K a b R : ℝ}
    {f : V × ℝ → E} (hf : HolderBound α {p : V × ℝ | ‖p.1‖<R ∧ p.2∈Icc a b} f K) :
    HolderBound α {p : V × ℝ | ‖p.1‖<R ∧ p.2∈Icc (-b) (-a)} (fun p => f (reflectTime p)) K := by
  have hm (p : V × ℝ) (hp : ‖p.1‖<R ∧ p.2∈Icc (-b) (-a)) :
      reflectTime p∈{p : V × ℝ | ‖p.1‖<R ∧ p.2∈Icc a b} :=
    ⟨hp.1,by dsimp [reflectTime]; constructor <;> linarith [hp.2.1,hp.2.2]⟩
  exact ⟨fun p hp => hf.1 _ (hm p hp),fun p hp q hq => by
    simpa only [pdist_reflect] using hf.2 _ (hm p hp) _ (hm q hq)⟩

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem exists_backward_model (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (g : C₀(V,ℂ)) (F : ℝ), 0≤F → ‖g‖≤F →
      (∀ x y, ‖g x-g y‖≤F*‖x-y‖^α) →
      ∃ v vt : ℝ → V → ℂ, (∀ x, v 0 x=0) ∧ (∀ x, vt 0 x=g x) ∧
        (∀ t∈Icc (-1/2:ℝ) 0, ContDiff ℝ 4 (v t)) ∧
        JetBound α {p : V × ℝ | ‖p.1‖<3 ∧ p.2∈Icc (-1/2:ℝ) 0} v vt (C*F) ∧
        (∀ t∈Icc (-1/2:ℝ) 0, ∀ x, HasDerivWithinAt (fun s => v s x)
          (vt t x) (Icc (-1/2:ℝ) 0) t) := by
  obtain ⟨C,hC,H⟩ := exists_initial_jet_model (V := V) α hα hα1
  refine ⟨C,hC,?_⟩
  intro g F hF hg hh
  obtain ⟨u,hu0,hs,hj,hd⟩ := H g F hF hg hh
  let v : ℝ → V → ℂ := fun t => -u (-t)
  let vt : ℝ → V → ℂ := fun t x => g x-Δ (Δ (u (-t))) x
  have ht (t : ℝ) (ht : t∈Icc (-1/2:ℝ) 0) : -t∈Icc 0 (1/2:ℝ) := by
    constructor <;> linarith [ht.1,ht.2]
  have hu0' : u 0=fun _ => (0:ℂ) := funext hu0
  refine ⟨v,vt,?_,?_,?_,⟨?_,?_⟩,?_⟩
  · intro x; simp [v,hu0]
  · intro x
    dsimp [vt]
    rw [neg_zero,hu0']
    have hz : Δ (0 : V → ℂ)=0 := InnerProductSpace.laplacian_const (c := (0:ℂ))
    rw [InnerProductSpace.laplacian_const,hz]
    simp
  · intro t h; exact (hs _ (ht t h)).neg
  · intro j hj4
    have H := (holder_reflect (hj.1 j hj4)).neg
    simpa only [neg_zero,neg_div,neg_neg,reflectTime,Prod.fst,Prod.snd,
      iteratedFDeriv_neg_apply,v,Pi.neg_apply] using H
  · have H := holder_reflect hj.2
    simpa only [neg_zero,neg_div,reflectTime,Prod.fst,Prod.snd,vt] using H
  · intro t h x
    have H := (hd (-t) (ht t h) x).scomp t ((hasDerivAt_neg t).hasDerivWithinAt
      (s := Icc (-1/2:ℝ) 0)) (fun s hs => ht s hs)
    convert H.neg using 1 <;> first | rfl | simp [vt]
end ParabolicInitial

end

end OAI
