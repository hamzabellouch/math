import Mathlib
import OAI.GroupTheory.FiniteType.DuffySimplex

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace SimplexRotation
open Set Topology
open scoped unitInterval
abbrev Std (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))
abbrev Boundary (n : ℕ) := {s : Std n // ∃ i, s.weights i = 0}
variable {n : ℕ}

def minimum (s : Std n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty s.weights

lemma minimum_nonneg (s : Std n) : 0 ≤ minimum s :=
  Finset.le_inf' _ _ (fun i _ => s.weights_nonneg i)
lemma minimum_le (s : Std n) (i : Fin (n+1)) : minimum s ≤ s.weights i :=
  Finset.inf'_le _ (Finset.mem_univ i)
lemma minimum_attained (s : Std n) : ∃ i, minimum s = s.weights i := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty s.weights
  exact ⟨i,hi⟩
lemma continuous_minimum : Continuous (minimum (n:=n)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => Convexity.StdSimplex.continuous_weights_apply ℝ i)
lemma minimum_boundary (s : Boundary n) : minimum s.1 = 0 := by
  obtain ⟨i,hi⟩ := s.2
  exact le_antisymm (by simpa only [hi] using minimum_le s.1 i) (minimum_nonneg s.1)

def radius (s : Std n) : ℝ := 1 - (n+1:ℕ)*minimum s

lemma radius_nonneg (s : Std n) : 0 ≤ radius s := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n+1)))) => minimum_le s i)
  simpa only [radius,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,s.total_of_fintype] using sub_nonneg.mpr h

lemma radius_zero_iff (s : Std n) : radius s = 0 ↔ ∀ i, s.weights i = minimum s := by
  constructor
  · intro h
    have hs : ∑ i, (s.weights i - minimum s) = 0 := by
      rw [Finset.sum_sub_distrib,s.total_of_fintype]
      simpa [radius] using h
    intro i
    exact sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (minimum_le s j))).mp hs i (Finset.mem_univ i))
  · intro h
    have hs := s.total_of_fintype
    simp only [h,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    exact sub_eq_zero.mpr hs.symm

lemma continuous_radius : Continuous (radius (n:=n)) :=
  continuous_const.sub (continuous_const.mul continuous_minimum)

def radial (s : Std n) (h : 0 < radius s) : Boundary n :=
  ⟨⟨Finsupp.equivFunOnFinite.symm (fun i => (s.weights i-minimum s)/radius s),by
    intro i
    exact div_nonneg (sub_nonneg.mpr (minimum_le s i)) h.le,by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i, (s.weights i-minimum s)/radius s = 1
    rw [← Finset.sum_div,Finset.sum_sub_distrib,s.total_of_fintype]
    simpa only [radius,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using div_self h.ne'⟩,by
    obtain ⟨i,hi⟩ := minimum_attained s
    exact ⟨i,by simp [hi]⟩⟩

lemma radial_boundary (s : Boundary n) (h : 0 < radius s.1) : radial s.1 h = s := by
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  simp [radial,radius,minimum_boundary]

def perm (p : Equiv.Perm (Fin (n+1))) : C(Std n,Std n) :=
  ⟨fun s => ⟨Finsupp.equivFunOnFinite.symm (fun i => s.weights (p i)),fun i => s.weights_nonneg _,by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact (Equiv.sum_comp p s.weights).trans s.total_of_fintype⟩,by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    exact Convexity.StdSimplex.continuous_weights_apply ℝ (p i)⟩

lemma perm_boundary (p : Equiv.Perm (Fin (n+1))) (s : Boundary n) :
    ∃ i, (perm p s.1).weights i = 0 := by
  obtain ⟨i,hi⟩ := s.2
  exact ⟨p.symm i,by simpa [perm] using hi⟩

def mix (p : Equiv.Perm (Fin (n+1))) : C(I × Std n,Std n) :=
  ⟨fun z => ⟨Finsupp.equivFunOnFinite.symm (fun i => (1-z.1:ℝ)*z.2.weights i+(z.1:ℝ)*z.2.weights (p i)),by
    intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.2.2) (z.2.weights_nonneg i))
      (mul_nonneg z.1.2.1 (z.2.weights_nonneg _)),by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i, ((1-z.1:ℝ)*z.2.weights i+(z.1:ℝ)*z.2.weights (p i)) = 1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
      Equiv.sum_comp,z.2.total_of_fintype]
    ring⟩,by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    change Continuous (fun z : I × Std n => (1-z.1:ℝ)*z.2.weights i+(z.1:ℝ)*z.2.weights (p i))
    have ht : Continuous (fun z : I × Std n => (z.1:ℝ)) := continuous_subtype_val.comp continuous_fst
    have hc (j : Fin (n+1)) : Continuous (fun z : I × Std n => z.2.weights j) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ j).comp continuous_snd
    exact ((continuous_const.sub ht).mul (hc i)).add (ht.mul (hc (p i)))⟩

@[simp] lemma mix_zero (p : Equiv.Perm (Fin (n+1))) (s : Std n) : mix p (0,s) = s := by
  apply Convexity.StdSimplex.ext; apply Finsupp.ext; intro i; simp [mix]
@[simp] lemma mix_one (p : Equiv.Perm (Fin (n+1))) (s : Std n) : mix p (1,s) = perm p s := by
  apply Convexity.StdSimplex.ext; apply Finsupp.ext; intro i; simp [mix,perm]

lemma mix_radius_pos (p : Equiv.Perm (Fin (n+1))) (hp : ∀ i, p (p (p i)) = i)
    (t : I) (s : Boundary n) : 0 < radius (mix p (t,s.1)) := by
  apply lt_of_le_of_ne (radius_nonneg _)
  intro hz
  have hc := (radius_zero_iff _).mp hz.symm
  let c := minimum (mix p (t,s.1))
  have hid (i : Fin (n+1)) : s.1.weights i = c := by
    have h0 := hc i
    have h1 := hc (p i)
    have h2 := hc (p (p i))
    change (1-t:ℝ)*s.1.weights i+(t:ℝ)*s.1.weights (p i) = c at h0
    change (1-t:ℝ)*s.1.weights (p i)+(t:ℝ)*s.1.weights (p (p i)) = c at h1
    change (1-t:ℝ)*s.1.weights (p (p i))+(t:ℝ)*s.1.weights (p (p (p i))) = c at h2
    rw [hp] at h2
    have hd : (0:ℝ) < (1-t:ℝ)^3+(t:ℝ)^3 := by
      nlinarith [sq_nonneg ((t:ℝ)-1/2)]
    apply (mul_left_cancel₀ (ne_of_gt hd))
    linear_combination (1-t:ℝ)^2*h0 - (t:ℝ)*(1-t)*h1+(t:ℝ)^2*h2
  obtain ⟨i,hi⟩ := s.2
  have hc0 : c = 0 := (hid i).symm.trans hi
  have hs := s.1.total_of_fintype
  simp only [hid,hc0,Finset.sum_const_zero] at hs
  norm_num at hs

def boundaryRotation (p : Equiv.Perm (Fin (n+1))) (hp : ∀ i, p (p (p i)) = i) :
    C(I × Boundary n,Boundary n) :=
  ⟨fun z => radial (mix p (z.1,z.2.1)) (mix_radius_pos p hp z.1 z.2),by
    apply Continuous.subtype_mk
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    apply Continuous.div
    · exact ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
        ((mix p).continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).sub
        (continuous_minimum.comp ((mix p).continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))))
    · exact continuous_radius.comp ((mix p).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    · intro z
      exact (mix_radius_pos p hp z.1 z.2).ne'⟩

@[simp] lemma boundaryRotation_zero (p : Equiv.Perm (Fin (n+1))) (hp : ∀ i, p (p (p i)) = i)
    (s : Boundary n) : boundaryRotation p hp (0,s) = s := by
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  simp [boundaryRotation,radial,mix_zero,radius,minimum_boundary]

@[simp] lemma boundaryRotation_one (p : Equiv.Perm (Fin (n+1))) (hp : ∀ i, p (p (p i)) = i)
    (s : Boundary n) : (boundaryRotation p hp (1,s)).1 = perm p s.1 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  have hm : minimum (perm p s.1) = 0 := minimum_boundary ⟨_,perm_boundary p s⟩
  simp [boundaryRotation,radial,mix_one,radius,hm]

end SimplexRotation

namespace RotationClass
open Set Topology SimplexRotation
open scoped unitInterval
universe u v
variable {X : Type u} [TopologicalSpace X] {Z : Type v} [TopologicalSpace Z]
variable {n : ℕ} {x : X}

def permute (f : BasedSimplex.Space n X x) (p : Equiv.Perm (Fin (n+1))) :
    BasedSimplex.Space n X x :=
  ⟨f.1.comp (perm p),fun s hs => f.2 _ (perm_boundary p ⟨s,hs⟩)⟩

def blend (a b : C(Z,Std n)) : C(I × Z,Std n) :=
  ⟨fun z => ⟨Finsupp.equivFunOnFinite.symm (fun i => (1-z.1:ℝ)*(a z.2).weights i+(z.1:ℝ)*(b z.2).weights i),by
    intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.2.2) ((a z.2).weights_nonneg i))
      (mul_nonneg z.1.2.1 ((b z.2).weights_nonneg i)),by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i, ((1-z.1:ℝ)*(a z.2).weights i+(z.1:ℝ)*(b z.2).weights i) = 1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
      (a z.2).total_of_fintype,(b z.2).total_of_fintype]
    ring⟩,by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    change Continuous (fun z : I × Z => (1-z.1:ℝ)*(a z.2).weights i+(z.1:ℝ)*(b z.2).weights i)
    have ht : Continuous (fun z : I × Z => (z.1:ℝ)) := continuous_subtype_val.comp continuous_fst
    have ha : Continuous (fun z : I × Z => (a z.2).weights i) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp (a.continuous.comp continuous_snd)
    have hb : Continuous (fun z : I × Z => (b z.2).weights i) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp (b.continuous.comp continuous_snd)
    exact ((continuous_const.sub ht).mul ha).add (ht.mul hb)⟩

@[simp] lemma blend_zero (a b : C(Z,Std n)) (z : Z) : blend a b (0,z) = a z := by
  apply Convexity.StdSimplex.ext; apply Finsupp.ext; intro i; simp [blend]
@[simp] lemma blend_one (a b : C(Z,Std n)) (z : Z) : blend a b (1,z) = b z := by
  apply Convexity.StdSimplex.ext; apply Finsupp.ext; intro i; simp [blend]
lemma blend_eq (a b : C(Z,Std n)) (z : Z) (h : a z = b z) (t : I) :
    blend a b (t,z) = b z := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  change (1-t:ℝ)*(a z).weights i+(t:ℝ)*(b z).weights i = (b z).weights i
  rw [h]
  ring

theorem class_of_boundary_isotopy (f : BasedSimplex.Space n X x)
    (p : Equiv.Perm (Fin (n+1)))
    (B : C(I × Boundary n,Boundary n))
    (h0 : ∀ s, B (0,s) = s)
    (h1 : ∀ s, (B (1,s)).1 = perm p s.1) :
    DuffyBased.homotopyClass f = DuffyBased.homotopyClass (permute f p) := by
  let side : C(I × Boundary n,Std n) := ⟨fun z => (B z).1,continuous_subtype_val.comp B.continuous⟩
  obtain ⟨F,hF0,hFs⟩ := SimplexHomotopy.exists_extension (ContinuousMap.id (Std n)) side
    (fun s => congrArg Subtype.val (h0 s))
  let g : C(Std n,Std n) := F.comp ⟨fun s => (1,s),continuous_const.prodMk continuous_id⟩
  have hg (s : Boundary n) : g s.1 = perm p s.1 := (hFs 1 s).trans (h1 s)
  let fg : BasedSimplex.Space n X x := ⟨f.1.comp g,fun s hs => by
    change f.1 (g s) = x
    rw [hg ⟨s,hs⟩]
    exact f.2 _ (perm_boundary p ⟨s,hs⟩)⟩
  have H : f.1.HomotopyRel fg.1 (BasedSimplex.Boundary n) :=
    { toHomotopy :=
      { toContinuousMap := f.1.comp F
        map_zero_left := fun s => congrArg f.1 (hF0 s)
        map_one_left := fun _ => rfl }
      prop' := by
        intro t s hs
        change f.1 (F (t,s)) = f.1 s
        rw [hFs t ⟨s,hs⟩]
        exact (f.2 _ (B (t,⟨s,hs⟩)).2).trans (f.2 s hs).symm }
  have K : fg.1.HomotopyRel (permute f p).1 (BasedSimplex.Boundary n) :=
    { toHomotopy :=
      { toContinuousMap := f.1.comp (blend g (perm p))
        map_zero_left := fun s => congrArg f.1 (blend_zero g (perm p) s)
        map_one_left := fun s => congrArg f.1 (blend_one g (perm p) s) }
      prop' := by
        intro t s hs
        change f.1 (blend g (perm p) (t,s)) = f.1 (g s)
        rw [blend_eq g (perm p) s (hg ⟨s,hs⟩) t,hg ⟨s,hs⟩] }
  exact (DuffyBased.class_eq_iff _ _).mpr ⟨H.trans K⟩

theorem class_cube (f : BasedSimplex.Space n X x) (p : Equiv.Perm (Fin (n+1)))
    (hp : ∀ i, p (p (p i)) = i) :
    DuffyBased.homotopyClass (permute f p) = DuffyBased.homotopyClass f :=
  (class_of_boundary_isotopy f p (boundaryRotation p hp)
    (boundaryRotation_zero p hp) (boundaryRotation_one p hp)).symm

@[simp] lemma permute_one (f : BasedSimplex.Space n X x) : permute f 1 = f := by
  apply Subtype.ext
  ext s
  change f.1 (perm 1 s) = f.1 s
  congr 1
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro index
  rfl

lemma permute_mul (f : BasedSimplex.Space n X x) (p q : Equiv.Perm (Fin (n+1))) :
    permute (permute f p) q = permute f (q*p) := by
  apply Subtype.ext
  ext s
  change f.1 (perm p (perm q s)) = f.1 (perm (q*p) s)
  rfl

end RotationClass

end

end OAI
