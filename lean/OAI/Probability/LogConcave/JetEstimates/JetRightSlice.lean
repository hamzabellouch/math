import Mathlib
import OAI.Probability.LogConcave.Sampling.JointSpace

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ : Type*}

lemma jet_right_slice_at {A : ℝ × E → ℝ} {t : ℝ}
    (hA : ∀y,ContDiffAt ℝ (⊤:ℕ∞) A (t,y)) (v : κ → E) (l : List κ) :
    jet v l (fun y => A (t,y))=fun y => jet (fun i => (0,v i)) l A (t,y) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    funext y
    exact dir_right_slice_at ((smooth_jet_at (hA y) _ l).differentiableAt (by simp)) _

lemma timeSmooth_jet {A : ℝ × E → ℝ} (hA : TimeSmooth A) (v : κ → ℝ × E) (l : List κ) :
    TimeSmooth (jet v l A) := fun p h0 h1 => smooth_jet_at (hA p h0 h1) v l

lemma timeSmooth_dir {A : ℝ × E → ℝ} (hA : TimeSmooth A) (v : ℝ × E) :
    TimeSmooth (dir v A) := fun p h0 h1 => smooth_dir_at (hA p h0 h1) v

end JetCalculus

lemma jointMean_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (i : Fin d) : JetCalculus.TimeSmooth (jointMean F x r i) := by
  intro p h0 h1
  exact jointMean_smooth_at hF x hr hl (by nlinarith) i

lemma jointScore_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (i : Fin d) : JetCalculus.TimeSmooth (jointScore F x r i) := by
  intro p h0 h1
  exact jointScore_smooth_at hF x hr hl (by nlinarith) i

lemma joint_mean_transport {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    (y : Point d) (i : Fin d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=
      ρ⁻¹*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => JetCalculus.dir (jointSpace k) (jointMean F x r i)) (ρ,y) := by
  have hp : ρ^2<1 := by nlinarith
  have hMi := jointMean_smooth_at hF x hr.le hl (p:=(ρ,y)) hp i
  have hm := joint_mdir_eq_material F x r (hMi.differentiableAt (by simp))
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=_ at hm
  rw [hm]
  change materialScalar F x r (fun t y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
    (conditionalFieldMean F x r t y)) ρ y=_
  rw [material_conditionalFieldMean hF x hr hlam hl hρ0.le hρ1]
  have he : (fun k y => conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i)
      ((lam:ℝ)*r) (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ k) [()])=
      fun k y => ρ⁻¹*JetCalculus.dir (EuclideanSpace.basisFun (Fin d) ℝ k)
        (fun z => jointMean F x r i (ρ,z)) y := by
    funext k
    exact conditionalU_one_eq_dir hF x hr hlam hl hρ0 hρ1 _ _
  have hD (k : Fin d) : Differentiable ℝ (JetCalculus.dir (EuclideanSpace.basisFun (Fin d) ℝ k)
      (fun z => jointMean F x r i (ρ,z))) :=
    (JetCalculus.smooth_dir ((innerSL ℝ _).contDiff.comp
      (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1)) _).differentiable (by simp)
  rw [he,tensorAdjoint_scalar _ _ hD]
  rw [joint_gadj_slice hF x hr.le hl hρ0.le hρ1 (fun k =>
    (JetCalculus.smooth_dir_at hMi _).differentiableAt (by simp))]
  have he' : (fun k => JetCalculus.dir (EuclideanSpace.basisFun (Fin d) ℝ k)
      (fun z => jointMean F x r i (ρ,z)))=
      fun k z => JetCalculus.dir (jointSpace k) (jointMean F x r i) (ρ,z) := by
    funext k z
    exact JetCalculus.dir_right_slice_at
      ((jointMean_smooth_at hF x hr.le hl (p:=(ρ,z)) hp i).differentiableAt (by simp)) _
  rw [he']

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma gadj_right_slice_at (b : ι → E) (s : ι → ℝ × E → ℝ)
    {V : ι → ℝ × E → ℝ} {t : ℝ} {y : E}
    (hV : ∀i,DifferentiableAt ℝ (V i) (t,y)) :
    gadj (fun i => (0,b i)) s V (t,y)=gadj b (fun i z => s i (t,z))
      (fun i z => V i (t,z)) y := by
  unfold gadj cadj
  apply Finset.sum_congr rfl
  intro i _
  rw [dir_right_slice_at (hV i)]

end JetCalculus

open JetCalculus in
theorem material_mean_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} [DecidableEq κ] (v : κ → Point d) (l : List κ) (hlN : l.Nodup)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (JetCalculus.jet (fun j => (0,v j)) l (jointMean F x r i)) (ρ,y)=
      ρ⁻¹*JetCalculus.gadj (JetCalculus.spaceBasis d) (fun k z => jointScore F x r k (ρ,z))
        (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k)
          (JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z)))) y+
        (l.length:ℝ)*ρ⁻¹*JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z)) y+
        2*r*∑s∈l.toFinset.powerset.erase ∅,∑k,
          JetCalculus.jet v (l.filter (fun j => j∈s)) (fun z => jointMean F x r k (ρ,z)) y*
            JetCalculus.dir (JetCalculus.spaceBasis d k)
              (JetCalculus.jet v (l.filter (fun j => j∉s)) (fun z => jointMean F x r i (ρ,z))) y := by
  have hp : ρ^2<1 := by nlinarith
  have hJ (k : Fin d) (z : Point d) : ContDiffAt ℝ (⊤:ℕ∞) (jointMean F x r k) (ρ,z) :=
    jointMean_smooth_at hF x hr.le hl hp k
  have hS (k : Fin d) : ContDiff ℝ (⊤:ℕ∞) (fun z => jointMean F x r k (ρ,z)) :=
    (innerSL ℝ _).contDiff.comp (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1)
  have hs (k : Fin d) (a : List κ) := JetCalculus.jet_right_slice_at (hJ k) v a
  have hds (k : Fin d) (a : List κ) (j : Fin d) (z : Point d) :
      JetCalculus.dir (jointSpace j) (JetCalculus.jet (fun j => (0,v j)) a (jointMean F x r k)) (ρ,z)=
      JetCalculus.dir (JetCalculus.spaceBasis d j)
        (JetCalculus.jet v a (fun z => jointMean F x r k (ρ,z))) z := by
    rw [hs]
    exact (JetCalculus.dir_right_slice_at
      ((JetCalculus.smooth_jet_at (hJ k z) _ a).differentiableAt (by simp)) _).symm
  have hbase : (fun z => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (jointMean F x r i) (ρ,z))=fun z =>
      ρ⁻¹*JetCalculus.gadj (JetCalculus.spaceBasis d)
        (fun k z => jointScore F x r k (ρ,z))
        (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k) (fun z => jointMean F x r i (ρ,z))) z := by
    funext z
    rw [joint_mean_transport hF x hr hlam hl hρ0 hρ1]
    have ht := JetCalculus.gadj_right_slice_at (JetCalculus.spaceBasis d) (jointScore F x r)
      (V:=fun k => JetCalculus.dir (jointSpace k) (jointMean F x r i))
      (fun k => (JetCalculus.smooth_dir_at (hJ i z) _).differentiableAt (by simp))
    change JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k => JetCalculus.dir (jointSpace k) (jointMean F x r i)) (ρ,z)=_ at ht
    rw [ht]
    have hd : (fun k w => JetCalculus.dir (jointSpace k) (jointMean F x r i) (ρ,w))=
        fun k => JetCalculus.dir (JetCalculus.spaceBasis d k) (fun w => jointMean F x r i (ρ,w)) := by
      funext k w
      exact hds i [] k w
    rw [hd]
  have hDj := JetCalculus.jet_right_slice_at (fun z => JetCalculus.smooth_mdir_at (1,0)
    jointSpace r (fun k => hJ k z) (hJ i z)) v l
  have hg : ContDiff ℝ (⊤:ℕ∞) (JetCalculus.gadj (JetCalculus.spaceBasis d)
      (fun k z => jointScore F x r k (ρ,z))
      (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k) (fun z => jointMean F x r i (ρ,z)))) :=
    ContDiff.sum fun k _ => JetCalculus.smooth_cadj _ (by
      change ContDiff ℝ (⊤:ℕ∞) (fun z => JetCalculus.linearScore k z+(r*ρ)*jointMean F x r k (ρ,z))
      exact (JetCalculus.linearScore_smooth k).add (contDiff_const.mul (hS k)))
      (JetCalculus.smooth_dir (hS i) _)
  have hj := congrFun (JetCalculus.jet_gadj_gradient hS (hS i) (r*ρ) v l hlN) y
  change JetCalculus.jet v l (JetCalculus.gadj (JetCalculus.spaceBasis d)
    (fun k z => jointScore F x r k (ρ,z))
    (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k) (fun z => jointMean F x r i (ρ,z)))) y=_ at hj
  rw [JetCalculus.mdir_jet_time _ _ _ (jointMean_timeSmooth hF x hr.le hl)
    (jointMean_timeSmooth hF x hr.le hl i) (fun j => (0,v j)) l hlN (by dsimp; linarith) hρ1]
  rw [←congrFun hDj y,hbase,JetCalculus.jet_const_mul hg]
  dsimp only
  rw [hj]
  have hsub : (∑s∈l.toFinset.powerset.erase ∅,∑k,
      JetCalculus.jet (fun j => (0,v j)) (l.filter (fun j => j∈s)) (jointMean F x r k) (ρ,y)*
        JetCalculus.dir (jointSpace k)
          (JetCalculus.jet (fun j => (0,v j)) (l.filter (fun j => j∉s)) (jointMean F x r i)) (ρ,y))=
      ∑s∈l.toFinset.powerset.erase ∅,∑k,
      JetCalculus.jet v (l.filter (fun j => j∈s)) (fun z => jointMean F x r k (ρ,z)) y*
        JetCalculus.dir (JetCalculus.spaceBasis d k)
          (JetCalculus.jet v (l.filter (fun j => j∉s)) (fun z => jointMean F x r i (ρ,z))) y := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro k _
    rw [←congrFun (hs k _) y,hds]
  rw [hsub]
  simp only [jointScore,JetCalculus.linearScore,JetCalculus.spaceBasis]
  field_simp [hρ0.ne']
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma mdir_time_at (b : ι → E) (r : ℝ) (M : ι → ℝ × E → ℝ)
    {c : ℝ → ℝ} {t : ℝ} (hc : DifferentiableAt ℝ c t) (y : E) :
    mdir (1,0) (fun i => (0,b i)) r M (fun p => c p.1) (t,y)=deriv c t := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × E => c p.1) (t,y) :=
    hc.comp (t,y) differentiableAt_fst
  unfold mdir
  rw [←dir_left_slice_at hd]
  have hs (i : ι) : dir (0,b i) (fun p : ℝ × E => c p.1) (t,y)=0 := by
    rw [←dir_right_slice_at hd]
    simp [dir]
  simp only [hs,mul_zero,Finset.sum_const_zero,sub_zero]

lemma mdir_time_mul_at (b : ι → E) (r : ℝ) (M : ι → ℝ × E → ℝ)
    {c : ℝ → ℝ} {A : ℝ × E → ℝ} {t : ℝ} {y : E}
    (hc : DifferentiableAt ℝ c t) (hA : DifferentiableAt ℝ A (t,y)) :
    mdir (1,0) (fun i => (0,b i)) r M (fun p => c p.1*A p) (t,y)=
      deriv c t*A (t,y)+c t*mdir (1,0) (fun i => (0,b i)) r M A (t,y) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × E => c p.1) (t,y) :=
    hc.comp (t,y) differentiableAt_fst
  rw [mdir_mul_at _ _ _ _ hd hA,mdir_time_at b r M hc]

lemma hasDerivAt_inv_nat_pow {t : ℝ} (ht : t≠0) (q : ℕ) :
    HasDerivAt (fun s : ℝ => (s^q)⁻¹) (-(q:ℝ)*t⁻¹*(t^q)⁻¹) t := by
  induction q with
  | zero => simpa using (hasDerivAt_const t (1:ℝ))
  | succ q ih =>
    have hh : HasDerivAt (fun s : ℝ => (s^q)⁻¹*s⁻¹)
        (-(q:ℝ)*t⁻¹*(t^q)⁻¹*t⁻¹+(t^q)⁻¹*(-1/t^2)) t :=
      ih.mul ((hasDerivAt_id t).inv ht)
    have hf : (fun s : ℝ => (s^(q+1))⁻¹)=fun s => (s^q)⁻¹*s⁻¹ := by
      funext s
      simp [pow_succ,mul_comm]
    rw [hf]
    have he : -(q:ℝ)*t⁻¹*(t^q)⁻¹*t⁻¹+(t^q)⁻¹*(-1/t^2)=
        -((q+1:ℕ):ℝ)*t⁻¹*(t^(q+1))⁻¹ := by
      simp only [Nat.cast_add,Nat.cast_one,pow_succ,mul_inv_rev]
      field_simp
      ring
    rwa [he] at hh

end LogConcaveSampling.JetCalculus

end

end

end

end OAI
