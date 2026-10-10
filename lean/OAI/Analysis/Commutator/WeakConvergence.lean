import Mathlib
import OAI.Analysis.Commutator.WeakOperatorLimit

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter

namespace Kadison.WeakOperatorLimit

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {l : Filter ι} {T : ι → H →L[ℂ] H} {V : H →L[ℂ] H}

def Converges (T : ι → H →L[ℂ] H) (V : H →L[ℂ] H) (l : Filter ι) : Prop :=
  ∀ x y, Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (V x) y))

lemma Converges.add {S : ι → H →L[ℂ] H} {W : H →L[ℂ] H}
    (hT : Converges T V l) (hS : Converges S W l) : Converges (T+S) (V+W) l := by
  intro x y
  simpa only [Pi.add_apply,add_apply,inner_add_left] using (hT x y).add (hS x y)

lemma Converges.sub {S : ι → H →L[ℂ] H} {W : H →L[ℂ] H}
    (hT : Converges T V l) (hS : Converges S W l) : Converges (T-S) (V-W) l := by
  intro x y
  simpa only [Pi.sub_apply,sub_apply,inner_sub_left] using (hT x y).sub (hS x y)

lemma converges_const (V : H →L[ℂ] H) : Converges (fun _ : ι => V) V l := fun _ _ => tendsto_const_nhds

lemma Converges.mul_right (hT : Converges T V l) (a : H →L[ℂ] H) :
    Converges (fun i => T i*a) (V*a) l := by
  intro x y
  exact hT (a x) y

lemma Converges.mul_left [CompleteSpace H] (hT : Converges T V l) (a : H →L[ℂ] H) :
    Converges (fun i => a*T i) (a*V) l := by
  intro x y
  simpa only [mul_apply_eq_comp,← ContinuousLinearMap.adjoint_inner_right a] using hT x (a.adjoint y)

lemma Converges.commutator [CompleteSpace H] (hT : Converges T V l) (a : H →L[ℂ] H) :
    Converges (fun i => T i*a-a*T i) (V*a-a*V) l :=
  (hT.mul_right a).sub (hT.mul_left a)

lemma Converges.unique [l.NeBot] {W : H →L[ℂ] H}
    (hT : Converges T V l) (hW : Converges T W l) : V=W := by
  ext x
  exact ext_inner_right ℂ (fun y => tendsto_nhds_unique (hT x y) (hW x y))

lemma Converges.eq_const [l.NeBot] (hT : Converges T V l) (W : H →L[ℂ] H)
    (hW : ∀ᶠ i in l, T i=W) : V=W := by
  apply hT.unique
  intro x y
  exact tendsto_const_nhds.congr' (hW.mono fun i h => by change inner ℂ (W x) y = inner ℂ (T i x) y; rw [h])

lemma Converges.norm [l.NeBot] (hT : Converges T V l) {C : ℝ} (hC : 0≤C)
    (hb : ∀ᶠ i in l, ‖T i‖≤C) : ‖V‖≤C := norm_le_of_tendsto hT hC hb

lemma Converges.commutes [CompleteSpace H] [l.NeBot] (hT : Converges T V l) (a : H →L[ℂ] H)
    (hb : ∀ᶠ i in l, T i*a=a*T i) : V*a=a*V := by
  apply sub_eq_zero.mp
  exact (hT.commutator a).eq_const 0 (hb.mono fun _ h => sub_eq_zero.mpr h)

lemma Converges.commutator_norm [CompleteSpace H] [l.NeBot] (hT : Converges T V l) (a : H →L[ℂ] H)
    {C : ℝ} (hC : 0≤C) (hb : ∀ᶠ i in l, ‖T i*a-a*T i‖≤C) : ‖V*a-a*V‖≤C :=
  (hT.commutator a).norm hC hb

lemma Converges.preserves_sandwich [CompleteSpace H] [l.NeBot] (hT : Converges T V l) (a b W : H →L[ℂ] H)
    (hb : ∀ᶠ i in l, a*T i*b=W) : a*V*b=W :=
  ((hT.mul_left a).mul_right b).eq_const W hb

lemma Converges.dist [l.NeBot] (hT : Converges T V l) (W : H →L[ℂ] H)
    {C : ℝ} (hC : 0≤C) (hb : ∀ᶠ i in l, ‖T i-W‖≤C) : ‖V-W‖≤C :=
  (hT.sub (converges_const W)).norm hC hb

end Kadison.WeakOperatorLimit

end

end
end

end OAI
