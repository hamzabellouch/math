import Mathlib
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

def cube (n : ℕ) (a b : ℝ) : Set (Fin n → ℝ) := Icc (fun _ => a) (fun _ => b)

def cubeIntegral {n : ℕ} (f : (Fin n → ℝ) → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in cube n a b, f x

lemma mem_cube {n : ℕ} {a b : ℝ} {x : Fin n → ℝ} :
    x ∈ cube n a b ↔ ∀ i, x i ∈ Icc a b := by
  simp only [cube, mem_Icc, Pi.le_def]
  exact forall_and.symm

lemma compact_cube (n : ℕ) (a b : ℝ) : IsCompact (cube n a b) := isCompact_Icc

lemma measurable_cube (n : ℕ) (a b : ℝ) : MeasurableSet (cube n a b) := measurableSet_Icc

lemma volume_cube_pos (n : ℕ) {a b : ℝ} (hab : a < b) : 0 < volume (cube n a b) := by
  simp only [cube, Real.volume_Icc_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pos_iff_ne_zero.mpr (pow_ne_zero _ (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne')

lemma cubeIntegral_positive {n : ℕ} {f : (Fin n → ℝ) → ℝ} {a b : ℝ}
    (hf : Continuous f) (hab : a < b) (hpos : ∀ x ∈ cube n a b, 0 < f x) :
    0 < cubeIntegral f a b := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_mem (measurable_cube _ _ _)).mono fun x hx => (hpos x hx).le)
    (hf.continuousOn.integrableOn_compact (compact_cube _ _ _))).mpr
  have heq : Function.support f ∩ cube n a b = cube n a b := by
    apply inter_eq_right.mpr
    intro x hx
    exact (hpos x hx).ne'
  rw [heq]
  exact volume_cube_pos n hab

lemma cubeIntegral_nonneg {n : ℕ} {f : (Fin n → ℝ) → ℝ} {a b : ℝ}
    (hpos : ∀ x ∈ cube n a b, 0 ≤ f x) : 0 ≤ cubeIntegral f a b := by
  exact integral_nonneg_of_ae
    ((ae_restrict_mem (measurable_cube _ _ _)).mono fun x hx => hpos x hx)

lemma fin_cons_mem_cube {n : ℕ} {a b x : ℝ} {y : Fin n → ℝ} :
    Fin.cons x y ∈ cube (n+1) a b ↔ x ∈ Icc a b ∧ y ∈ cube n a b := by
  simp only [mem_cube, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]

lemma cubeIntegral_zero (f : (Fin 0 → ℝ) → ℝ) (a b : ℝ) :
    cubeIntegral f a b = f (fun i => Fin.elim0 i) := by
  have heq : cube 0 a b = univ := by
    ext x
    simp only [mem_cube, mem_univ, iff_true]
    intro i
    exact Fin.elim0 i
  have hv : (volume : Measure (Fin 0 → ℝ)) univ = 1 := by
    change (Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ))) univ = 1
    simp
  have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
    funext x
    congr 1
    exact Subsingleton.elim _ _
  rw [cubeIntegral, heq, setIntegral_univ, hf, integral_const]
  simp [Measure.real, hv]

lemma continuous_cube_marginal {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Continuous f) (a b : ℝ) :
    Continuous (fun t : ℝ => cubeIntegral (fun x => f (Fin.cons t x)) a b) := by
  apply continuous_parametric_integral_of_continuous
  · exact hf.comp (continuous_fst.finCons (A := fun _ : Fin (n+1) => ℝ) continuous_snd)
  · exact compact_cube _ _ _

lemma cubeIntegral_succ {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ} {a b : ℝ}
    (hf : Continuous f) (hab : a ≤ b) :
    cubeIntegral f a b = ∫ t in a..b, cubeIntegral (fun x => f (Fin.cons t x)) a b := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he (z : ℝ × (Fin n → ℝ)) : e z = Fin.cons z.1 z.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.zero_succAbove]
  have hpre : e ⁻¹' cube (n+1) a b = Icc a b ×ˢ cube n a b := by
    ext z
    simp only [mem_preimage, he, fin_cons_mem_cube, mem_prod]
  have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  unfold cubeIntegral
  rw [← hpres.setIntegral_preimage_emb e.measurableEmbedding f (cube (n+1) a b)]
  change (∫ z in e ⁻¹' cube (n+1) a b, f (e z)) = _
  simp_rw [hpre, he]
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod]
  · rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  · exact (hf.comp (continuous_fst.finCons continuous_snd)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (compact_cube _ _ _))

theorem cube_prekopa_leindler (n : ℕ) {a b s t : ℝ}
    {f g h : (Fin n → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hab : a < b) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1)
    (hfpos : ∀ x ∈ cube n a b, 0 < f x) (hgpos : ∀ x ∈ cube n a b, 0 < g x)
    (hnonneg : ∀ z ∈ cube n a b, 0 ≤ h z)
    (hcomb : ∀ x ∈ cube n a b, ∀ y ∈ cube n a b,
      (f x)^s*(g y)^t ≤ h (s • x+t • y)) :
    (cubeIntegral f a b)^s*(cubeIntegral g a b)^t ≤ cubeIntegral h a b := by
  induction n with
  | zero =>
    simp only [cubeIntegral_zero]
    have hzero : (fun i : Fin 0 => Fin.elim0 i) ∈ cube 0 a b :=
      mem_cube.mpr fun i => Fin.elim0 i
    have he := hcomb _ hzero _ hzero
    convert he using 1
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    let F : ℝ → ℝ := fun u => cubeIntegral (fun x => f (Fin.cons u x)) a b
    let G : ℝ → ℝ := fun u => cubeIntegral (fun x => g (Fin.cons u x)) a b
    let H : ℝ → ℝ := fun u => cubeIntegral (fun x => h (Fin.cons u x)) a b
    have hF : Continuous F := continuous_cube_marginal hf _ _
    have hG : Continuous G := continuous_cube_marginal hg _ _
    have hH : Continuous H := continuous_cube_marginal hh _ _
    have hleft : s*a+t*a=a := by rw [← add_mul, hst, one_mul]
    have hright : s*b+t*b=b := by rw [← add_mul, hst, one_mul]
    have hFpos (u : ℝ) (hu : u ∈ Ioo a b) : 0 < F u := by
      apply cubeIntegral_positive (hf.comp (continuous_const.finCons continuous_id)) hab
      intro x hx
      exact hfpos _ (fin_cons_mem_cube.mpr ⟨Ioo_subset_Icc_self hu, hx⟩)
    have hGpos (u : ℝ) (hu : u ∈ Ioo a b) : 0 < G u := by
      apply cubeIntegral_positive (hg.comp (continuous_const.finCons continuous_id)) hab
      intro x hx
      exact hgpos _ (fin_cons_mem_cube.mpr ⟨Ioo_subset_Icc_self hu, hx⟩)
    have hHnonneg (u : ℝ) (hu : u ∈ Icc (s*a+t*a) (s*b+t*b)) : 0 ≤ H u := by
      rw [hleft, hright] at hu
      apply cubeIntegral_nonneg
      intro x hx
      exact hnonneg _ (fin_cons_mem_cube.mpr ⟨hu, hx⟩)
    have hFGH (u : ℝ) (hu : u ∈ Ioo a b) (v : ℝ) (hv : v ∈ Ioo a b) :
        (F u)^s*(G v)^t ≤ H (s*u+t*v) := by
      have hc : s*u+t*v ∈ Icc a b := by
        constructor
        · rw [← hleft]
          exact add_le_add (mul_le_mul_of_nonneg_left hu.1.le hs) (mul_le_mul_of_nonneg_left hv.1.le ht)
        · rw [← hright]
          exact add_le_add (mul_le_mul_of_nonneg_left hu.2.le hs) (mul_le_mul_of_nonneg_left hv.2.le ht)
      apply ih (hf.comp (continuous_const.finCons continuous_id))
        (hg.comp (continuous_const.finCons continuous_id))
        (hh.comp (continuous_const.finCons continuous_id))
      · intro x hx
        exact hfpos _ (fin_cons_mem_cube.mpr ⟨Ioo_subset_Icc_self hu, hx⟩)
      · intro x hx
        exact hgpos _ (fin_cons_mem_cube.mpr ⟨Ioo_subset_Icc_self hv, hx⟩)
      · intro x hx
        exact hnonneg _ (fin_cons_mem_cube.mpr ⟨hc, hx⟩)
      · intro x hx y hy
        have heq : s • Fin.cons u x+t • Fin.cons v y = Fin.cons (s*u+t*v) (s • x+t • y) := by
          funext i
          exact Fin.cases (by rfl) (fun j => by rfl) i
        simpa only [heq, Function.comp_apply, id_eq] using hcomb _ (fin_cons_mem_cube.mpr ⟨Ioo_subset_Icc_self hu, hx⟩)
          _ (fin_cons_mem_cube.mpr ⟨Ioo_subset_Icc_self hv, hy⟩)
    have hPL := interval_weighted_prekopa_leindler hF hG hH hFpos hGpos hab hab hs ht hst hHnonneg hFGH
    rw [hleft, hright] at hPL
    simpa only [cubeIntegral_succ hf hab.le, cubeIntegral_succ hg hab.le, cubeIntegral_succ hh hab.le]
      using hPL

end FacetVolume

end

end OAI
