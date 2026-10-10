import OAI.Geometry.Convex.GeneralMahler.Hermite.Gradient

namespace OAI
/-! Parseval identities for finite-dimensional Gaussian fields and bilinear pairings. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ} [NeZero m]
variable {F E:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A measurable field with polynomial growth. -/
structure regular (f:Rn m→F) : Prop where
  p : PolyBound f
  meas : AEStronglyMeasurable f (normal m)
namespace regular
variable {f:Rn m→F} (hf:regular f)
omit [NeZero m] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
lemma ig (hf:regular f) : Integrable f (normal m) :=
  hf.p.gaussian_integrable hf.meas
omit [NeZero m] [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] in
lemma lin (hf:regular f) (l:F→L[ℝ]E) :
    regular (fun x=>l (f x)) := ⟨(PolyBound.clm _).comp hf.p,(l.integrable_comp hf.ig).aestronglyMeasurable⟩
omit [NeZero m] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
lemma add {g:Rn m→F} (hf:regular f) (hg:regular g) : regular fun x=>f x+g x :=
  ⟨hf.p.add hg.p,hf.meas.add hg.meas⟩
omit [NeZero m] [FiniteDimensional ℝ F] in
lemma smul (hf:regular f) {g:Rn m→ℝ} (hg:regular g) : regular fun x=>g x • f x :=
  ⟨hg.p.smul hf.p,hg.meas.smul hf.meas⟩
omit [NeZero m] in
lemma mul {f g:Rn m→ℝ} (hf:regular f) (hg:regular g) : regular fun x=>f x*g x := hg.smul hf
end regular

variable {f:Rn m→E} {g:Rn m→F}
omit [NeZero m] in
lemma cof_clm (hf:regular f) (l:E→L[ℝ]F) (a:MI m) : l (cof f a)=cof (fun x=>l (f x)) a := by
  unfold cof
  rw [← l.integral_comp_comm (i_cof hf.p hf.meas a)]
  simp only [map_smul]
lemma cof_form (hf:regular f) (hg:regular g) (l:E→L[ℝ]ℝ) (k:F→L[ℝ]ℝ) :
    HasSum (fun a=> l (cof f a)*k (cof g a))
      (∫ x,l (f x)*k (g x) ∂normal m) := by
  have hi := hf.lin l
  have hh := hg.lin k
  simp_rw [cof_clm hf,cof_clm hg,← qcf_cof]
  exact qcf_sum (lp_poly hi.p hi.meas) (lp_poly hh.p hh.meas)

-- Function of a bilinear form, prove via finite-dimensional basis projections
lemma cof_bil (hf:regular f) (hg:regular g) (l:E→L[ℝ]F→L[ℝ]ℝ) :
    HasSum (fun a=>l (cof f a) (cof g a)) (∫ x,l (f x) (g x) ∂normal m) := by
  let b := Module.finBasis ℝ E
  let c := fun i=> (b.coord i).toContinuousLinearMap
  have he (x:E) (y:F) : l x y= ∑ i,c i x*l (b i) y := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [_root_.map_sum,_root_.sum_apply,_root_.map_smul,_root_.smul_apply,smul_eq_mul]
    rfl
  have h (i) := cof_form hf hg (c i) (l (b i))
  rw [show (fun x=> l (f x) (g x))=_ from funext (fun x=> he (f x) (g x)), show (fun a=> l (cof f a) (cof g a))=_ from funext (fun x=> he (cof f x) (cof g x))]
  rw [integral_finsetSum]
  · exact hasSum_sum fun i _=> h i
  exact fun i _=> ((hf.lin (c i)).mul (hg.lin (l (b i)))).ig

lemma cof_vec (f g:Rn m→Rn m) (hf:regular f) (hg:regular g) :
    HasSum (fun a=>⟪cof f a,cof g a⟫) (∫ x,⟪f x,g x⟫ ∂normal m) :=
  cof_bil hf hg (innerSL ℝ)

-- degree/shift arithmetic
def deg (a:MI m) := ∑ i,a i
omit [NeZero m] in
lemma deg_inc (a:MI m) (i) : deg (inc a i)=deg a+1 := by
  simp only [deg,inc]
  classical
  simp only [← Finset.sum_erase_add _ _ (Finset.mem_univ i),Function.update_self]
  have hi : (∑ k∈Finset.univ.erase i,Function.update a i (a i+1) k) =
      ∑ k∈Finset.univ.erase i,a k := Finset.sum_congr rfl fun k hk=> Function.update_of_ne
        (Finset.ne_of_mem_erase hk) ..
  rw [hi]; omega
omit [NeZero m] in
lemma dz (a:MI m) : deg a=0 ↔ a=0 := by
  unfold deg; simp [Finset.sum_eq_zero_iff,funext_iff]
omit [NeZero m] in
lemma dec_inc (a:MI m) (i:Fin m) : decM (inc a i) i=a := by
  ext j
  by_cases h:i=j
  · subst j; simp [inc, decM]
  simp [inc,decM,Ne.symm h]
omit [NeZero m] in
lemma inc_dec (a:MI m) (i:Fin m) (hi:a i≠0) : inc (decM a i) i=a := by
  ext j
  by_cases h:i=j
  · subst j; simp [inc, decM]; omega
  simp [inc,decM,Ne.symm h]
def userS (i:Fin m) := {a:MI m| a i≠0}
def incE (i:Fin m) : MI m ≃ userS i where
  toFun a := ⟨inc a i, by unfold userS inc; simp⟩
  invFun a := decM a.val i
  left_inv a := dec_inc a i
  right_inv a := Subtype.ext (inc_dec _ _ a.property)

omit [NeZero m] in
lemma inc_sum (i:Fin m) (a:MI m→ℝ) (he:∀ x:MI m,x i=0→a x=0) :
    (Summable a ↔ Summable fun x=>a (inc x i)) ∧
    (∑' x,a x)=∑' x,a (inc x i) := by
  classical
  have h : Function.support a⊆userS i := fun x hx hs=> hx (he x hs)
  -- reindex via embedding
  have hi (t:ℝ) : HasSum a t ↔ HasSum (fun x=>a (inc x i)) t := by
    let l := incE i
    have he : (fun x=> a (inc x i))=(fun x:userS i=> a x.val) ∘ l := rfl
    rw [he,l.hasSum_iff]
    exact (hasSum_subtype_iff_of_support_subset h).symm
  have he' : Summable a ↔ Summable fun x=>a (inc x i) := exists_congr hi
  refine ⟨he',?_⟩
  by_cases hs:Summable a
  · exact (HasSum.tsum_eq ((hi _).mp hs.hasSum)).symm
  rw [tsum_eq_zero_of_not_summable hs,tsum_eq_zero_of_not_summable (he'.not.mp hs)]

omit [NeZero m] in
lemma iDeg (a:MI m) (i) : a i ≤ deg a :=
  Finset.single_le_sum (fun k _=> Nat.zero_le (a k)) (Finset.mem_univ i)

omit [NeZero m] in
lemma sum_spectral (C:MI m→ℝ) (hh:C 0=0) (hs:Summable C) :
    ∑' a,C a = ∑ i:Fin m,∑' a, C (inc a i)*((a i+1:ℕ):ℝ)/(1+deg a) := by
  let f (i:Fin m) (a:MI m) := (C a*((a i:ℕ):ℝ))/(deg a:ℝ)
  have hf (a:MI m) : C a=∑ i,f i a := by
    unfold f; rw [← Finset.sum_div,← Finset.mul_sum,show (∑ i:Fin m,(a i:ℝ)) = (deg a:ℝ)
      from by simp [deg]]
    rcases eq_or_ne (deg a) 0 with h|h
    · rw [h, Nat.cast_zero,div_zero]; exact dz a |>.mp h ▸ hh
    have hp : (deg a:ℝ)≠0 := by exact_mod_cast h
    field_simp
  have hi (i:Fin m) : Summable (f i) := by
    apply Summable.of_norm_bounded hs.norm
    intro a
    unfold f; rw [norm_div,norm_mul]; norm_cast
    have hv := iDeg a i
    by_cases hj:deg a=0
    · simp [hj]
    have hp : 0 < (deg a:ℝ) := by positivity
    rw [div_le_iff₀ hp]
    gcongr
  have he (i:Fin m) := inc_sum i (f i) (fun x hx=>by simp [f,hx])
  calc
    _ = ∑' a,∑ i,f i a := tsum_congr hf
    _ = ∑ i,∑' a,f i a := Summable.tsum_finsetSum (fun i _=>hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(he i).2]
      apply tsum_congr; intro a; unfold f; rw [inc_at,deg_inc]; push_cast; ring
end GeneralMahler.HMode

end

end OAI
