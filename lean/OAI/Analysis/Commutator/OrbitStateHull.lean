import Mathlib
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.WeakDualHull
import OAI.Analysis.Commutator.VonNeumannCStar
import OAI.Analysis.Commutator.ProjectionDimensionUnitary
import OAI.Analysis.Commutator.DyadicDimensionNormal

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def vector (x : H) : StrongDual ℂ M :=
  LinearMap.mkContinuous
    { toFun := fun a => inner ℂ x ((a : H →L[ℂ] H) x)
      map_add' := by
        intro a b
        change inner ℂ x ((a : H →L[ℂ] H) x+(b : H →L[ℂ] H) x)=_
        exact inner_add_right _ _ _
      map_smul' := by
        intro c a
        change inner ℂ x (c • (a : H →L[ℂ] H) x)=c*inner ℂ x ((a : H →L[ℂ] H) x)
        exact inner_smul_right _ _ _ }
    (‖x‖*‖x‖) (by
      intro a
      calc
        _ ≤ ‖x‖*‖(a : H →L[ℂ] H) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖*(‖a‖*‖x‖) := mul_le_mul_of_nonneg_left ((a : H →L[ℂ] H).le_opNorm x) (norm_nonneg x)
        _ = ‖x‖*‖x‖*‖a‖ := by ring)

@[simp] lemma vector_apply (x : H) (a : M) :
    vector M x a=inner ℂ x ((a : H →L[ℂ] H) x) := rfl

lemma vector_norm (x : H) : ‖vector M x‖≤‖x‖*‖x‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_self_nonneg _) _

lemma vector_nonneg (x : H) {a : M} (ha : 0≤a) : 0≤vector M x a :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp ha).inner_nonneg_right x

def orbit (x : H) : Set (WeakDual ℂ M) :=
  {f | ∃ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H)∈M ∧
    f=(vector M ((u : H →L[ℂ] H) x)).toWeakDual}

def hull (x : H) : Set (WeakDual ℂ M) := WeakDualHull.hull (orbit M x)

lemma vector_mem_hull (x : H) : (vector M x).toWeakDual∈hull M x := by
  apply WeakDualHull.subset_hull
  exact ⟨1,M.one_mem,rfl⟩

lemma hull_nonempty (x : H) : (hull M x).Nonempty := ⟨_,vector_mem_hull M x⟩

lemma hull_compact (x : H) : IsCompact (hull M x) := by
  apply WeakDualHull.compact_hull (‖x‖*‖x‖) (mul_self_nonneg _)
  rintro f ⟨u,_,rfl⟩
  simpa only [StrongDual.toStrongDual_toWeakDual,Unitary.norm_map] using vector_norm M ((u : H →L[ℂ] H) x)

lemma hull_norm (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x) :
    ‖f.toStrongDual‖≤‖x‖*‖x‖ := by
  apply WeakDualHull.norm_le (‖x‖*‖x‖) (mul_self_nonneg _) _ hf
  rintro g ⟨u,_,rfl⟩
  simpa only [StrongDual.toStrongDual_toWeakDual,Unitary.norm_map] using vector_norm M ((u : H →L[ℂ] H) x)

lemma hull_one (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x) :
    f 1=(‖x‖^2 : ℝ) := by
  apply WeakDualHull.eval_eq (1 : M) ((‖x‖^2 : ℝ) : ℂ) _ hf
  rintro g ⟨u,_,rfl⟩
  change inner ℂ ((u : H →L[ℂ] H) x) ((u : H →L[ℂ] H) x)=_
  rw [inner_self_eq_norm_sq_to_K,Unitary.norm_map,Complex.ofReal_pow]
  rfl

lemma hull_nonneg (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x)
    {a : M} (ha : 0≤a) : 0≤f a := by
  apply WeakDualHull.eval_nonneg a _ hf
  rintro g ⟨u,_,rfl⟩
  exact vector_nonneg M _ ha

def positive (x : H) (f : WeakDual ℂ M) (hf : f∈hull M x) : M →ₚ[ℂ] ℂ where
  toLinearMap := f.toStrongDual.toLinearMap
  monotone' := by
    intro a b hab
    apply sub_nonneg.mp
    change 0≤f.toStrongDual b-f.toStrongDual a
    rw [←map_sub]
    exact hull_nonneg M x hf (sub_nonneg.mpr hab)

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (hfac : FactorCorner.IsFactor M) (hd : DiffuseProjection.HasNoMinimalProjections M)

variable (hfin : IsFiniteAlgebra M)

include hfac hd hfin

theorem hull_projection_absolute_continuity (x : H) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ p : M,IsStarProjection (p : H →L[ℂ] H) →
      dimension M hfac hd p<δ → ∀ f∈hull M x,‖f p‖≤ε := by
  obtain ⟨δ,hδ,hp⟩ := orbit_vector_uniform_absolute_continuity M hfac hd hfin x
    (ε/(‖x‖+1)) (div_pos hε (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro p hproj hdim f hf
  apply WeakDualHull.eval_norm_le p ε _ hf
  rintro g ⟨u,hu,rfl⟩
  have hv := hp p p.property hproj hdim u hu
  calc
    _ ≤ ‖(u : H →L[ℂ] H) x‖*‖(p : H →L[ℂ] H) ((u : H →L[ℂ] H) x)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖*(ε/(‖x‖+1)) := by
      rw [Unitary.norm_map]
      exact mul_le_mul_of_nonneg_left hv.le (norm_nonneg x)
    _ ≤ (‖x‖+1)*(ε/(‖x‖+1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ε := mul_div_cancel₀ ε (by positivity)

theorem hull_projection_tendsto (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x)
    (p : M) (hp : IsStarProjection (p : H →L[ℂ] H)) (P : ℕ → M)
    (hP : ∀ n,IsStarProjection ((P n : M) : H →L[ℂ] H))
    (hmono : Monotone (fun n => ((P n : M) : H →L[ℂ] H)))
    (hPp : ∀ n,(P n : H →L[ℂ] H)≤(p : H →L[ℂ] H))
    (hlim : ∀ y,Tendsto (fun n => (P n : H →L[ℂ] H) y) atTop (𝓝 ((p : H →L[ℂ] H) y))) :
    Tendsto (fun n => f (P n)) atTop (𝓝 (f p)) := by
  have hdlim := dimension_tendsto_of_strong_increasing M hfac hd hfin p.property hp
    (fun n => (P n : H →L[ℂ] H)) (fun n => (P n).property) hP hmono hPp hlim
  have hdiff : Tendsto (fun n => dimension M hfac hd ((p-P n : M) : H →L[ℂ] H)) atTop (𝓝 0) := by
    have he (n : ℕ) : dimension M hfac hd ((p-P n : M) : H →L[ℂ] H)=
        dimension M hfac hd p-dimension M hfac hd (P n) :=
      dimension_difference M hfac hd hfin p.property (P n).property hp (hP n) (hPp n)
    simp_rw [he]
    simpa only [sub_self] using (tendsto_const_nhds (x := dimension M hfac hd p)).sub hdlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδp⟩ := hull_projection_absolute_continuity M hfac hd hfin x (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (hdiff.eventually_lt_const hδ)
  refine ⟨N,?_⟩
  intro n hn
  have hb := hδp (p-P n) ((hP n).le_iff_sub hp |>.mp (hPp n)) (hN n hn) f hf
  rw [map_sub,norm_sub_rev] at hb
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_norm] using lt_of_le_of_lt hb (by linarith : ε/2<ε)

end Kadison.OrbitStateHull

end

end
end

end OAI
