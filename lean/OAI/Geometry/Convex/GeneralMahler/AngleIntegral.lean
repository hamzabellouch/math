import OAI.Geometry.Convex.GeneralMahler.InTail

namespace OAI
/-! Diagonal balance, with separate estimates at the two ends of the coordinate box. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers ProjField
variable {m : ℕ} [NeZero m]

-- Polynomial coefficient D as in angle_est.
def ek (j : ℝ) := Real.exp (-(j^2)/4)

lemma ekpos (j:ℝ) : 0 ≤ ek j := Real.exp_nonneg _
lemma ekrapid : rapid ek := by
  convert rapid_exp_sq (show 0<(1/4:ℝ) by norm_num) using 1
  ext x
  unfold ek; ring_nf
lemma small_minus_bound (m : ℕ) [NeZero m] {D:ℝ} (hd:0≤D) :
    ∃ W≥0, ∀ q:ProjField m, ∀ v:Rn m, ‖v‖=1 → ∀ R:ℝ, 2≤R →
    (∀ z j:ℝ, 1≤j → q.dimH v z ≤ D*(j/R*a z + ek j)) →
    q.minus v ≤ W := by
  let b := fun z:ℝ => (phi z * (1+‖z‖) + ek z)
  let c := fun z:ℝ => D*b z
  have hb : PolyBound (fun z:ℝ => 1+‖z‖) :=
    (PolyBound.const _).add PolyBound.id.norm
  have hm : Measurable ek := by unfold ek; fun_prop
  have hf : Integrable b := ((rapid_phi.product hb).integrable_real
    (by have h := (by unfold phi; fun_prop : Measurable phi); fun_prop)).add
    (ekrapid.integrable_real hm)
  refine ⟨∫ z,c z,?_, fun q v hv R hr h => ?_⟩
  · exact integral_nonneg fun z=>mul_nonneg hd
      (add_nonneg (mul_nonneg (phi_pos z).le (by positivity)) (ekpos _))
  change ∫ z in Iio (0:ℝ), q.dimH v z ≤ _
  have hI : Integrable c := hf.const_mul _
  apply le_trans _ (setIntegral_le_integral (s:=Iio 0) hI
    (ae_of_all _ fun z=>mul_nonneg hd
      (add_nonneg (mul_nonneg (phi_pos z).le (by positivity)) (ekpos _))))
  apply setIntegral_mono_on (q.minus_int v hv) hI.integrableOn measurableSet_Iio
  intro z hz
  apply le_trans (h z (1+‖z‖) (by have h := norm_nonneg z; linarith))
  apply mul_le_mul_of_nonneg_left _ hd
  apply add_le_add
  · rw [mul_comm (phi z)]
    have hA := a_high (-z) (by change z<0 at hz; linarith)
    rw [neg_neg, neg_phi] at hA
    exact mul_le_mul (div_le_self (by positivity) (show 1 ≤ R by linarith)) hA (a_pos z).le (by positivity)
  apply Real.exp_le_exp.mpr
  rw [Real.norm_eq_abs,abs_of_neg (mem_Iio.mp hz)]
  change z<0 at hz
  nlinarith

lemma small_plus_lower {D : ℝ} (q:ProjField m) (v:Rn m) (hv:‖v‖=1)
    {L R N : ℝ} (hd:0≤D) (hr:0<R) (hN : 1 ≤ N) (hl:0≤L)
    (h:∀ z:ℝ, q.dimH v z ≤ D*(N/R*a z+ek N))
    (hh:D*(N/R*a L+ek N) ≤ 1/2) :
    L*(1/2) ≤ q.plus v := by
  let s := Icc 0 L
  let f := fun z=>1-q.dimH v z
  have hi : IntegrableOn f (Ici 0) := q.plus_int v hv
  have hs : s ⊆ Ici 0 := Icc_subset_Ici_self
  apply le_trans _ (setIntegral_mono_set hi
    (ae_of_all _ fun z=> sub_nonneg.mpr (q.h_between v hv z).2)
    (Filter.Eventually.of_forall hs))
  have hL : (∫ _ : ℝ in s,(1/2:ℝ))=L*(1/2) := by
    rw [setIntegral_const]
    simp [s,Real.volume_real_Icc_of_le hl]
  rw [← hL]
  refine setIntegral_mono_on (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
    (hi.mono_set hs) measurableSet_Icc (fun z hz=>?_)
  have he : q.dimH v z ≤ 1/2 := le_trans (h z)
    (le_trans (show D*(N/R*a z+ek N) ≤ _ from
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (a_mono.monotone hz.2) (by positivity)) le_rfl) hd) hh)
  unfold f; linarith

lemma large_minus_lower {D R N : ℝ} (hr:0<R) (x:Param m R) (q₀:ProjField m)
    (v:Rn m) (hv:‖v‖=1) (hd:0≤D) (hN : 1 ≤ N)
    (hh:D*(N/R*(4/a (-1))+ek N) ≤ 1/2) :
    let q := x.instanceQ hr q₀
    (∀ z:ℝ, 1-q.dimH v z ≤ D*(N/R*q.Bt z+ek N)) →
      1/2 ≤ q.minus v := by
  intro q h
  let s := Ico (-1:ℝ) 0
  have hi := q.minus_int v hv
  have hs : s ⊆ Iio 0 := Ico_subset_Iio_self
  apply le_trans _ (setIntegral_mono_set hi (ae_of_all _ fun z=>(q.h_between v hv z).1)
    (Filter.Eventually.of_forall hs))
  have hL : (∫ _ : ℝ in s,(1/2:ℝ))=1/2 := by
    rw [setIntegral_const]
    norm_num [s,Real.volume_real_Ico]
  rw [← hL]
  refine setIntegral_mono_on (integrableOn_const
    (hs := (lt_of_le_of_lt (measure_mono Ico_subset_Icc_self)
      isCompact_Icc.measure_lt_top).ne)) (hi.mono_set hs) measurableSet_Ico ?_
  intro z hz
  have he : 1-q.dimH v z ≤ 1/2 := le_trans (h z)
    (le_trans (show D*(N/R*q.Bt z+ek N) ≤ _ from
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (x.B_segment hr q₀ z hz.1) (by positivity)) le_rfl) hd) hh)
  linarith

lemma large_core_upper {D R L N:ℝ} (hr:0<R) (x:Param m R) (q₀:ProjField m)
    (v:Rn m) (hv:‖v‖=1) (hd:0≤D) (hN:1≤N) (hl:0≤L) :
    let q := x.instanceQ hr q₀
    (∀ z, 1-q.dimH v z ≤ D*(N/R*q.Bt z+ek N)) →
    (∫ z in Icc (0:ℝ) L, (1-q.dimH v z)) ≤ D*N/R*8 + D*ek N*L := by
  intro q hh
  have h := x.area_B hr q₀
  have hi : IntegrableOn q.Bt (Ici 0) := h.1
  let s := Icc 0 L
  have hs : s ⊆ Ici 0 := Icc_subset_Ici_self
  have ha : IntegrableOn (fun z : ℝ=>D*N/R*q.Bt z) s := (hi.mono_set hs).const_mul _
  have hb : IntegrableOn (fun _ : ℝ=>D*ek N) s := integrableOn_const
    (hs := isCompact_Icc.measure_lt_top.ne)
  have he : (∫ z in s,q.Bt z) ≤ 8 := le_trans (setIntegral_mono_set hi
    (ae_of_all _ q.Bt_nonneg) (Filter.Eventually.of_forall hs)) h.2
  let f := fun z=>1-q.dimH v z
  have hf : IntegrableOn f s := (q.plus_int v hv).mono_set hs
  calc
    _ ≤ ∫ z in s,(D*N/R*q.Bt z+D*ek N) :=
      setIntegral_mono_on hf (ha.add hb) measurableSet_Icc
        (fun z _=> (hh z).trans_eq (by ring))
    _ = D*N/R*(∫ z in s,q.Bt z)+D*ek N*L := by
      rw [integral_add ha hb, integral_const_mul,setIntegral_const]
      simp [s,Real.volume_real_Icc_of_le hl,mul_comm]
    _ ≤ _ := by gcongr

lemma plus_split (q:ProjField m) (v:Rn m) (hv:‖v‖=1) {L : ℝ} (hl:0≤L) :
    let f := fun z=>1-q.dimH v z
    q.plus v = (∫ z in Icc 0 L,f z)+(∫ z in Ioi L, f z) := by
  intro f
  have he : Icc 0 L ∪ Ioi L = Ici 0 := by
    ext z
    change ((0≤z ∧ z≤L) ∨ L<z) ↔ _
    simp only [mem_Ici]
    grind
  have hi : IntegrableOn f (Ici 0) := q.plus_int v hv
  rw [← he] at hi
  change (∫ z in Ici 0,f z) = _
  rw [← he]
  refine setIntegral_union ?_ measurableSet_Ioi (hi.mono_set subset_union_left)
    (hi.mono_set subset_union_right)
  exact disjoint_left.mpr fun z hz hh=> not_lt_of_ge hz.2 hh
end GeneralMahler

end

end OAI
