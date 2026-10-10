import Mathlib

namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate
open Matrix
open scoped Topology BigOperators

variable {R V : Type*} [Fintype R] [Fintype V]

def region (A : Matrix R V ℝ) (b : R → ℝ) : Set (V → ℝ) :=
  {x | ∀ r, ∑ j, A r j * x j ≤ b r}

omit [Fintype R] in
lemma row_perturb (A : Matrix R V ℝ) (x u : V → ℝ) (r : R) (t : ℝ) :
    (∑ j, A r j * (x j+t*u j)) = (∑ j, A r j*x j)+t*(∑ j, A r j*u j) := by
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem active_kernel_zero (A : Matrix R V ℝ) (b : R → ℝ) (x : V → ℝ)
    (hx : x ∈ (region A b).extremePoints ℝ) (u : V → ℝ)
    (hu : ∀ r, (∑ j, A r j*x j)=b r → (∑ j, A r j*u j)=0) : u=0 := by
  have hn : ∀ᶠ t : ℝ in 𝓝 0, (fun j => x j+t*u j) ∈ region A b := by
    apply Filter.eventually_all.mpr
    intro r
    by_cases ha : (∑ j, A r j*x j)=b r
    · exact Filter.Eventually.of_forall (fun t => by rw [row_perturb,hu r ha,ha]; simp)
    · have hs : (∑ j, A r j*x j)<b r := lt_of_le_of_ne (hx.1 r) ha
      have hc : Continuous (fun t : ℝ => ∑ j, A r j*(x j+t*u j)) := by fun_prop
      have hh : ∀ᶠ t : ℝ in 𝓝 0, (∑ j, A r j*(x j+t*u j))<b r :=
        hc.continuousAt.eventually_lt_const (by simpa using hs)
      exact hh.mono (fun _ h => h.le)
  obtain ⟨e,he,hs⟩ := Metric.eventually_nhds_iff.mp hn
  have hp : (fun j => x j+(e/2)*u j) ∈ region A b := hs (by simpa [abs_of_pos he] using (show e/2<e by linarith))
  have hm : (fun j => x j+(-e/2)*u j) ∈ region A b := hs (by simpa [abs_of_pos he] using (show e/2<e by linarith))
  have hmid : midpoint ℝ (fun j => x j+(e/2)*u j) (fun j => x j+(-e/2)*u j) = x := by
    rw [midpoint_eq_smul_add]
    ext j
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,invOf_eq_inv]
    ring
  have hseg := midpoint_mem_openSegment (𝕜 := ℝ) (fun j => x j+(e/2)*u j) (fun j => x j+(-e/2)*u j)
  rw [hmid] at hseg
  have heq := hx.2 hp hm hseg
  ext j
  have hh := congrFun heq j
  change u j=0
  have hmul : (e/2)*u j=0 := by linarith
  exact (mul_eq_zero.mp hmul).resolve_left (by positivity)

omit [Fintype R] in
lemma region_closed (A : Matrix R V ℝ) (b : R → ℝ) : IsClosed (region A b) := by
  have h : region A b = ⋂ r, {x : V → ℝ | (∑ j, A r j*x j) ≤ b r} := by
    ext x
    simp only [region,Set.mem_ofPred_eq,Set.mem_iInter]
  rw [h]
  apply isClosed_iInter
  intro r
  exact isClosed_le (by fun_prop) continuous_const

theorem bounded_extreme (A : Matrix R V ℝ) (b : R → ℝ) (B : ℝ)
    (hn : (region A b).Nonempty)
    (hbound : ∀ x ∈ region A b, ∀ j, -B ≤ x j ∧ x j ≤ B) :
    ∃ x ∈ region A b, ∀ u : V → ℝ,
      (∀ r, (∑ j, A r j*x j)=b r → (∑ j, A r j*u j)=0) → u=0 := by
  have hc : IsCompact (region A b) :=
    isCompact_Icc.of_isClosed_subset (region_closed A b) (by
      intro x hx
      exact ⟨fun j => (hbound x hx j).1,fun j => (hbound x hx j).2⟩)
  obtain ⟨x,hx⟩ := hc.extremePoints_nonempty hn
  exact ⟨x,hx.1,fun u hu => active_kernel_zero A b x hx u hu⟩

lemma gram_det_ne_zero [DecidableEq V] (C : Matrix R V ℝ)
    (hker : ∀ u : V → ℝ, C *ᵥ u=0 → u=0) : (Cᵀ*C).det≠0 := by
  classical
  have hg : ∀ u : V → ℝ, (Cᵀ*C) *ᵥ u=0 → u=0 := by
    intro u hu
    have hsum : ∑ r, (C *ᵥ u) r ^ 2 = 0 := by
      calc
        _ = u ⬝ᵥ ((Cᵀ*C) *ᵥ u) := by
          rw [←mulVec_mulVec,dotProduct_transpose_mulVec]
          simp only [dotProduct,pow_two]
        _ = 0 := by rw [hu]; simp
    have hz : ∀ r, (C *ᵥ u) r=0 := by
      intro r
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun r (_ : r ∈ Finset.univ) => sq_nonneg ((C *ᵥ u) r))).mp hsum r (Finset.mem_univ r)
      exact sq_eq_zero_iff.mp hh
    exact hker u (funext hz)
  have hi : Function.Injective (Cᵀ*C).mulVec := by
    intro u w huw
    have hh : (Cᵀ*C) *ᵥ (u-w)=0 := by rw [mulVec_sub,huw,sub_self]
    exact sub_eq_zero.mp (hg _ hh)
  exact isUnit_iff_ne_zero.mp ((Cᵀ*C).isUnit_iff_isUnit_det.mp (mulVec_injective_iff_isUnit.mp hi))

lemma abs_det_le [DecidableEq V] (M : Matrix V V ℤ) (H : ℤ)
    (hM : ∀ i j, |M i j| ≤ H) :
    |M.det| ≤ (Fintype.card V).factorial * H^(Fintype.card V) := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ s : Equiv.Perm V, |(s.sign : ℤ) * ∏ i, M (s i) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : Equiv.Perm V, H^(Fintype.card V) := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul,Equiv.Perm.sign_abs,one_mul,Finset.abs_prod]
      calc
        _ ≤ ∏ _i : V, H := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun index _ => hM (s index) index)
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]

omit [Fintype R] in
lemma int_det_cast [DecidableEq V] (M : Matrix V V ℤ) :
    ((M.det:ℤ):ℝ)=Matrix.det (fun i j => (M i j:ℝ)) := by
  exact (Int.castRingHom ℝ).map_det M

theorem integer_point_certificate [DecidableEq V] (A : Matrix R V ℤ) (b : R → ℤ)
    (H : ℤ) (hH : 0 ≤ H) (hA : ∀ r j, |A r j| ≤ H) (hb : ∀ r, |b r| ≤ H)
    (x : V → ℝ)
    (hker : ∀ u : V → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)=(b r:ℝ) →
      (∑ j, (A r j:ℝ)*u j)=0) → u=0) :
    ∃ p : V → ℤ, ∃ q : ℤ, q≠0 ∧
      |q| ≤ (Fintype.card V).factorial * ((Fintype.card R:ℤ)*H^2)^(Fintype.card V) ∧
      (∀ j, |p j| ≤ (Fintype.card V).factorial * ((Fintype.card R:ℤ)*H^2)^(Fintype.card V)) ∧
      (fun j => (p j:ℝ)/(q:ℝ)) = x := by
  classical
  let active (r : R) : Prop := (∑ j, (A r j:ℝ)*x j)=(b r:ℝ)
  let C : Matrix R V ℤ := fun r j => if active r then A r j else 0
  let d : R → ℤ := fun r => if active r then b r else 0
  let G : Matrix V V ℤ := Cᵀ*C
  let c : V → ℤ := Cᵀ *ᵥ d
  let Cr : Matrix R V ℝ := fun r j => (C r j:ℝ)
  let Gr : Matrix V V ℝ := fun i j => (G i j:ℝ)
  have hm : Gr=Crᵀ*Cr := by
    ext i j
    change ((∑ r, C r i*C r j:ℤ):ℝ) = _
    push_cast
    rfl
  have hcx : Cr *ᵥ x = fun r => (d r:ℝ) := by
    ext r
    by_cases ha : active r
    · simpa only [Matrix.mulVec,dotProduct,Cr,C,d,ite_eq_left ha] using ha
    · simp [Matrix.mulVec,dotProduct,Cr,C,d,ha]
  have hc : (fun j => (c j:ℝ))=Crᵀ *ᵥ (fun r => (d r:ℝ)) := by
    ext j
    change ((∑ r, C r j*d r:ℤ):ℝ) = _
    push_cast
    rfl
  have hdet : Gr.det≠0 := by
    rw [hm]
    apply gram_det_ne_zero
    intro u hu
    apply hker u
    intro r hr
    have hh := congrFun hu r
    simpa only [Matrix.mulVec,dotProduct,Cr,C,ite_eq_left (show active r from hr),Pi.zero_apply] using hh
  have hgx : Gr *ᵥ x = fun j => (c j:ℝ) := by
    rw [hm,←mulVec_mulVec,hcx,←hc]
  have hq : G.det≠0 := by
    intro hh
    apply hdet
    rw [←int_det_cast,hh,Int.cast_zero]
  have hcramer : (Gr.det) • x = Gr.cramer (fun j => (c j:ℝ)) := by
    rw [cramer_eq_adjugate_mulVec,←hgx,mulVec_mulVec,adjugate_mul,smul_mulVec,one_mulVec]
  have hxrat : ∀ j, x j = ((G.updateCol j c).det:ℝ)/(G.det:ℝ) := by
    intro j
    have hh := congrFun hcramer j
    simp only [Pi.smul_apply,smul_eq_mul,cramer_apply] at hh
    have hmap : (fun i k => ((G.updateCol j c) i k:ℝ))=Gr.updateCol j (fun k => (c k:ℝ)) := by
      ext i k
      simp only [Matrix.updateCol_apply]
      split_ifs <;> rfl
    have hcast : (Gr.updateCol j (fun k => (c k:ℝ))).det = ((G.updateCol j c).det:ℝ) := by
      rw [←hmap,←int_det_cast]
    have hcastG : Gr.det=(G.det:ℝ) := (int_det_cast G).symm
    rw [hcast,hcastG] at hh
    apply (eq_div_iff (by exact_mod_cast hq)).mpr
    linarith
  have hC : ∀ r j, |C r j|≤H := by
    intro r j
    by_cases ha : active r
    · simpa only [C,ite_eq_left ha] using hA r j
    · simpa only [C,ite_eq_right ha,abs_zero] using hH
  have hd : ∀ r, |d r|≤H := by
    intro r
    by_cases ha : active r
    · simpa only [d,ite_eq_left ha] using hb r
    · simpa only [d,ite_eq_right ha,abs_zero] using hH
  have hG : ∀ i j, |G i j| ≤ (Fintype.card R:ℤ)*H^2 := by
    intro i j
    calc
      _ = |∑ r, C r i*C r j| := rfl
      _ ≤ ∑ r, |C r i*C r j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, H^2 := by
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul,pow_two]
        exact mul_le_mul (hC r i) (hC r j) (abs_nonneg _) hH
      _ = _ := by simp
  have hcv : ∀ j, |c j| ≤ (Fintype.card R:ℤ)*H^2 := by
    intro j
    calc
      _ = |∑ r, C r j*d r| := rfl
      _ ≤ ∑ r, |C r j*d r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, H^2 := by
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul,pow_two]
        exact mul_le_mul (hC r j) (hd r) (abs_nonneg _) hH
      _ = _ := by simp
  refine ⟨fun j => (G.updateCol j c).det,G.det,hq,
    abs_det_le G _ hG,?_,?_⟩
  · intro j
    apply abs_det_le _ _
    intro i k
    by_cases he : k=j
    · simpa only [Matrix.updateCol_apply,he,ite_true] using hcv i
    · simpa only [Matrix.updateCol_apply,he,ite_false] using hG i k
  · ext j
    exact (hxrat j).symm

end MetricKMedianRecovery.PolytopeCertificate

end OAI
