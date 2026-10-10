import Mathlib
import OAI.Probability.LogConcave.JetEstimates.TensorTerm

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorSum
variable {S T : Type}
lemma weightLE_pure (A : TensorAtom S) {w : ℕ} (h : A.expression.weight≤w) :
    (pure A).weightLE w := fun _ => h
lemma weightLE_add {A B : TensorSum S} {w : ℕ} (hA : A.weightLE w) (hB : B.weightLE w) :
    (A.add B).weightLE w := by
  intro i; cases i with
  | inl i => exact hA i
  | inr i => exact hB i
lemma weightLE_scale {A : TensorSum S} {w : ℕ} (hA : A.weightLE w) (n : ℕ) (P : Polynomial ℝ) :
    (A.scale n P).weightLE w := hA
lemma weightLE_relabel {A : TensorSum S} {w : ℕ} (hA : A.weightLE w) (e : S ≃ T) :
    (A.relabel e).weightLE w := hA
lemma weightLE_adjoint [Fintype S] (hn : 2≤Fintype.card S) {A : TensorSum (S ⊕ Unit)}
    {w : ℕ} (hA : A.weightLE w) : (A.adjoint hn).weightLE (w+1) := by
  intro i
  change ((A.term i).atom.adjoint hn).expression.weight≤w+1
  rw [TensorAtom.adjoint_weight]
  exact Nat.add_le_add_right (hA i) 1
lemma weightLE_contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    {A : TensorSum (S ⊕ Unit)} {B : TensorSum (T ⊕ Unit)} {w z : ℕ}
    (hA : A.weightLE w) (hB : B.weightLE z) : (A.contract B).weightLE (w+z) := by
  intro i
  change ((A.term i.1).atom.contract (B.term i.2).atom).expression.weight≤w+z
  rw [TensorAtom.contract_weight]
  exact Nat.add_le_add (hA _) (hB _)
lemma weightLE_mono {A : TensorSum S} {w z : ℕ} (hA : A.weightLE w) (h : w≤z) :
    A.weightLE z := fun i => (hA i).trans h
end TensorSum

namespace TensorAtom
variable {S T : Type}

def HasMaterial (A : TensorAtom S) (B : TensorSum S) : Prop :=
  ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}, Primitive F lam →
    ∀(x : Point d) {r ρ : ℝ}, 0<r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 →
      ∀(c : S → Fin d) (y : Point d),
        JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
          (A.eval F x r ((lam:ℝ)*r) c) (ρ,y)=B.eval F x r ((lam:ℝ)*r) c (ρ,y)

lemma timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (A : TensorAtom S) (c : S → Fin d) :
    JetCalculus.TimeSmooth (A.eval F x r ((lam:ℝ)*r) c) :=
  A.expression.jointEval_timeSmooth hF x hr hlam hl _

lemma HasMaterial.relabel {A : TensorAtom S} {B : TensorSum S} (h : A.HasMaterial B) (e : S ≃ T) :
    (A.relabel e).HasMaterial (B.relabel e) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  exact h hF x hr hlam hl h0 h1 (c ∘ e) y

lemma HasMaterial.contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    {A : TensorAtom (S ⊕ Unit)} {B : TensorAtom (T ⊕ Unit)}
    {DA : TensorSum (S ⊕ Unit)} {DB : TensorSum (T ⊕ Unit)}
    (hA : A.HasMaterial DA) (hB : B.HasMaterial DB) :
    (A.contract B).HasMaterial ((DA.contract (TensorSum.pure B)).add ((TensorSum.pure A).contract DB)) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  have hsA (k : Fin d) := A.timeSmooth hF x hr hlam hl
    (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have hsB (k : Fin d) := B.timeSmooth hF x hr hlam hl
    (Sum.elim (fun s => c (Sum.inr s)) (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have he : (A.contract B).eval F x r ((lam:ℝ)*r) c=fun p =>
      ∑k : Fin d,A.eval F x r ((lam:ℝ)*r) (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) p*
        B.eval F x r ((lam:ℝ)*r) (Sum.elim (fun s => c (Sum.inr s)) (fun _ => k)) p :=
    funext (contract_eval A B F x r _ c)
  rw [he,JetCalculus.mdir_sum_at Finset.univ _ _ _ _ (fun k _ => ((hsA k).mul (hsB k)).differentiableAt (by simp))]
  simp_rw [JetCalculus.mdir_mul_at _ _ _ _ ((hsA _).differentiableAt (by simp)) ((hsB _).differentiableAt (by simp)),
    hA hF x hr hlam hl h0 h1,hB hF x hr hlam hl h0 h1]
  rw [TensorSum.add_eval,TensorSum.contract_eval,TensorSum.contract_eval]
  simp_rw [TensorSum.pure_eval]
  exact Finset.sum_add_distrib

lemma HasMaterial.adjoint [Fintype S] [Nonempty S] (hn : 2≤Fintype.card S)
    {A : TensorAtom (S ⊕ Unit)} {DA : TensorSum (S ⊕ Unit)} (hA : A.HasMaterial DA) :
    (A.adjoint hn).HasMaterial ((DA.adjoint hn).add
      ((TensorSum.pure (A.insertOne.adjoint hn)).scale 1 Polynomial.X)) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  let L : ℝ := (lam:ℝ)*r
  let V : Fin d → ℝ × Point d → ℝ := fun k => A.eval F x r L (Sum.elim c (fun _ => k))
  let W : Fin d → ℝ × Point d → ℝ := fun k => DA.eval F x r L (Sum.elim c (fun _ => k))
  have hV (k : Fin d) : ContDiffAt ℝ (⊤:ℕ∞) (V k) (ρ,y) :=
    A.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1
  have hW (k : Fin d) : ContDiffAt ℝ (⊤:ℕ∞) (W k) (ρ,y) :=
    DA.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1
  have hp : ρ^2<1 := by nlinarith
  have hM := jointMean_smooth_at hF x hr.le hl (p:=(ρ,y)) hp
  have hda : JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (V k)) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r) W (ρ,y) := by
    apply JetCalculus.gadj_slice_congr_at _
    · intro k; exact (JetCalculus.smooth_mdir_at _ _ _ hM (hV k)).differentiableAt (by simp)
    · intro k; exact (hW k).differentiableAt (by simp)
    · intro k z; exact hA hF x hr hlam hl h0 h1 _ z
  let I : Fin d → ℝ × Point d → ℝ := fun k => A.insertOne.eval F x r L (Sum.elim c (fun _ => k))
  have hI (k : Fin d) : ContDiffAt ℝ (⊤:ℕ∞) (I k) (ρ,y) :=
    A.insertOne.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1
  have hdi : JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k p => ∑i,JetCalculus.dir (jointSpace i) (jointMean F x r k) p*V i p) (ρ,y)=
      L*ρ*JetCalculus.gadj jointSpace (jointScore F x r) I (ρ,y) := by
    rw [←JetCalculus.gadj_scalar_at _ _ (fun k => (hI k).differentiableAt (by simp)) (L*ρ)]
    apply JetCalculus.gadj_slice_congr_at _
    · intro k; exact (ContDiffAt.sum (fun i _ =>
        (JetCalculus.smooth_dir_at (hM k) _).mul (hV i))).differentiableAt (by simp)
    · intro k; exact (contDiffAt_const.mul (hI k)).differentiableAt (by simp)
    · intro k z
      have hh := insertOne_mean hF x hr hlam hl h0 h1 A (Sum.elim c (fun _ => k)) z
      simpa only [Sum.elim_inl,Sum.elim_inr] using hh
  rw [adjoint_eval,physical_material_adjoint_nonneg hF x hr hlam hl h0 h1 hV]
  change JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (V k)) (ρ,y)+
      r*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k p => ∑i,JetCalculus.dir (jointSpace i) (jointMean F x r k) p*V i p) (ρ,y)=_
  rw [hda,hdi,TensorSum.add_eval,TensorSum.adjoint_eval hF x hr hlam hl h0 h1,
    TensorSum.scale_eval,TensorSum.pure_eval,adjoint_eval]
  simp only [pow_one,Polynomial.eval_X]
  dsimp only [W,I,L]
  ring

end TensorAtom
end LogConcaveSampling

end

end

end

end OAI
