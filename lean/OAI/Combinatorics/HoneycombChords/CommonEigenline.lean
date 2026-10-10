import OAI.Combinatorics.HoneycombChords.ClosedFusion
import OAI.Combinatorics.HoneycombChords.StripExhaustion

namespace OAI

/-! The physical common eigenline and its crossing observable.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open BoundaryJet Filter Topology
open scoped Matrix
lemma marked_double_mixed_ports (H m : ℕ) :
    both ((markedDoubleMatrix H^m) (fun _=>1) (fun _=>1))=
      ∑ j : Fin (2*m),∑ k : Fin (2*m),
      prescribedPartition H (2*m) (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1) := by
  rw [markedDoubleMatrix_eq,←pow_mul,marked_power_mixed]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact prescribed_transpose _ _ _ _ _ _

theorem source_marked_coefficient_limit (W : ℕ) :
    Tendsto (fun m : ℕ=>
      (both ((markedDoubleMatrix (W+1)^m) (fun _=>1) (fun _=>1))).re/(m:ℝ)) atTop
      (𝓝 (2*∑' γ : StrictBridge (W+1),kappa^γ.val.length)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have ht : Tendsto (fun m : ℕ=>2*m+1) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro m
    dsimp
    omega
  have hh:=(StripExhaustion.physical_rectangle_average_limit W).comp ht
  have hl:=hh.const_mul 2
  convert hl using 1
  funext m
  dsimp only [Function.comp_apply]
  rw [marked_double_mixed_ports,Complex.re_sum]
  simp only [Complex.re_sum]
  have hn : 2*(m+1)=2*m+1+1 := by omega
  have hs := congrArg (fun n : ℕ=>∑ j : Fin n,∑ k : Fin n,
    (prescribedPartition (W+1) n (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)).re) hn
  rw [hs,Finset.sum_comm]
  have hc : ((2*m+1+1:ℕ):ℝ)=2*((m+1:ℕ):ℝ) := by push_cast;ring
  rw [hc]
  ring
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open BoundaryJet Filter Topology
open scoped Matrix
lemma markedProjection_vacuum_base (W : ℕ) :
    base (markedProjection W (fun _=>1) (fun _=>1))=1 := by
  have hh:=congrFun (congrFun (markedProjection_base W) (fun _=>1)) (fun _=>1)
  exact hh.trans (projection_vacuum W)
lemma marked_vacuum_coefficient (W m : ℕ) :
    both ((markedDoubleMatrix (W+1)^(m+1)) (fun _=>1) (fun _=>1))=
      ((m+1:ℕ):ℂ)*eigenCoefficient W+
      both (markedProjection W (fun _=>1) (fun _=>1))+
      both ((markedRemainder W^(m+1)) (fun _=>1) (fun _=>1)) := by
  rw [marked_power_split,markedEigenvalue_pow]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,both_add,both_mul,
    base_form,left_form,right_form,both_form,one_mul,zero_mul,add_zero,
    markedProjection_vacuum_base,mul_one]
  ring

theorem marked_eigenvalue_limit (W : ℕ) :
    Tendsto (fun m : ℕ=>both ((markedDoubleMatrix (W+1)^m) (fun _=>1) (fun _=>1))/(m:ℂ))
      atTop (𝓝 (eigenCoefficient W)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hr : Tendsto (fun m : ℕ=>both ((markedRemainder W^(m+1)) (fun _=>1) (fun _=>1)))
      atTop (𝓝 0) := by
    have hh:=tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (marked_remainder_limit W) (fun _=>1)) (fun _=>1)
    have hq:=(continuous_both.tendsto 0).comp (hh.comp (tendsto_add_atTop_nat 1))
    simpa [Function.comp_def,both] using hq
  have hi : Tendsto (fun m : ℕ=>(((m+1:ℕ):ℂ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have hd:=((tendsto_const_nhds (x:=both (markedProjection W (fun _=>1) (fun _=>1)))).add hr).mul hi
  have hl:=(tendsto_const_nhds (x:=eigenCoefficient W)).add hd
  simp only [add_zero,mul_zero] at hl
  convert hl using 1
  funext m
  rw [marked_vacuum_coefficient]
  have hm : ((m+1:ℕ):ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp
  ring
lemma rectangular_ports_im_zero (W n : ℕ) :
    (∑ j : Fin n,∑ k : Fin n,
      prescribedPartition (W+1) n (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)).im=0 := by
  classical
  cases n with
  | zero => simp
  | succ n =>
    simp only [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    rw [actual_chord_sum_eq_transfer]
    simp only [Complex.im_sum,←Complex.ofReal_pow,Complex.ofReal_im,Finset.sum_const_zero]
lemma marked_coefficient_real (W m : ℕ) :
    ((both ((markedDoubleMatrix (W+1)^m) (fun _=>1) (fun _=>1))).re:ℂ)=
      both ((markedDoubleMatrix (W+1)^m) (fun _=>1) (fun _=>1)) := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    rw [marked_double_mixed_ports,rectangular_ports_im_zero]

theorem source_eigenvalue_eq_twice_bridge_mass (W : ℕ) :
    eigenCoefficient W=2*((∑' γ : StrictBridge (W+1),kappa^γ.val.length):ℝ) := by
  have hl:=(Complex.continuous_ofReal.tendsto
    (2*∑' γ : StrictBridge (W+1),kappa^γ.val.length)).comp (source_marked_coefficient_limit W)
  have hc : Tendsto (fun m : ℕ=>both ((markedDoubleMatrix (W+1)^m) (fun _=>1) (fun _=>1))/(m:ℂ))
      atTop (𝓝 (2*((∑' γ : StrictBridge (W+1),kappa^γ.val.length):ℝ))) := by
    simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_natCast,
      marked_coefficient_real,Complex.ofReal_mul,Complex.ofReal_ofNat] using hl
  exact tendsto_nhds_unique (marked_eigenvalue_limit W) hc
end CriticalHoneycomb.Transfer.RasterGrid

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
noncomputable def reorient (n : ℕ) (M : Matrix (Space n) (Space n) Jet) :
    Matrix (Space n) (Space n) Jet :=
  (M.submatrix (reflectedSites n) (reflectedSites n)).map reflectJet
lemma reorient_mul (n : ℕ) (M N : Matrix (Space n) (Space n) Jet) :
    reorient n (M*N)=reorient n M*reorient n N := by
  unfold reorient
  rw [Matrix.submatrix_mul _ _ _ _ _ (reflectedSites n).bijective,Matrix.map_mul]
lemma physicalFamily_commute (n : ℕ) (u v : ℝ)
    (hu : Nonsingular n (homogeneous n) u) (hv : Nonsingular n (homogeneous n) v) :
    Commute (physicalFamily n u) (physicalFamily n v) := by
  have h:=congrArg (reorient n) (source_global_spectral_commutation n (homogeneous n) u v hu hv).eq
  change reorient n (T n (homogeneous n) u)*reorient n (T n (homogeneous n) v)=
    reorient n (T n (homogeneous n) v)*reorient n (T n (homogeneous n) u)
  simpa only [reorient_mul] using h
noncomputable def physicalScalar (W : ℕ) (u : ℝ) : Jet :=
  commonScalar W (physicalFamily (W+1) u)
theorem physical_common_line (W : ℕ) (u : ℝ)
    (hu : Nonsingular (W+1) (homogeneous (W+1)) u) :
    physicalFamily (W+1) u*ᵥmarkedEigenvector W=
      physicalScalar W u•markedEigenvector W := by
  apply commuting_common_line
  rw [←physicalFamily_at_gamma]
  exact physicalFamily_commute (W+1) gamma u (homogeneous_nonsingular _) hu
lemma physicalScalar_at_gamma (W : ℕ) : physicalScalar W gamma=markedEigenvalue W := by
  unfold physicalScalar commonScalar
  rw [physicalFamily_at_gamma,source_marked_eigenvector]
  change (∑ s,normalizedDual W s*(markedEigenvalue W*markedEigenvector W s))=_
  calc
    _=markedEigenvalue W*(normalizedDual W ⬝ᵥ markedEigenvector W) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _=markedEigenvalue W := by rw [normalized_pair,mul_one]
lemma physicalScalar_mass (W : ℕ) :
    both (physicalScalar W gamma)=2*((∑' γ : StrictBridge (W+1),kappa^γ.val.length):ℝ) := by
  rw [physicalScalar_at_gamma,markedEigenvalue,both_form]
  exact source_eigenvalue_eq_twice_bridge_mass W
lemma physicalScalar_reflection (W : ℕ) (u : ℝ)
    (hu : Nonsingular (W+1) (homogeneous (W+1)) u) :
    physicalScalar W (b-u)=physicalScalar W u := by
  unfold physicalScalar physicalFamily
  rw [source_spectral_reflection _ _ u hu]
lemma physicalScalar_periodicity (W : ℕ) (u : ℝ) :
    physicalScalar W (u+Real.pi)=physicalScalar W u := by
  unfold physicalScalar physicalFamily
  rw [source_spectral_periodicity]
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators
lemma seedAux_eq (k : ℂ) (f : DiluteState) :
    act (boundaryWeights k) 0 (addAux f) = seedAux k f := by
  funext xs
  cases xs with
  | nil => rfl
  | cons a xs => cases xs with
    | nil => rfl
    | cons b xs =>
      simp only [act,Fintype.sum_option,Fintype.sum_bool,addAux,mul_zero,add_zero]
      exact congrArg (fun z => z * f xs) (boundary_input k a b)

def rowGates : ℕ → List TileWeights → List (TileWeights × ℕ)
  | _, [] => []
  | i, t::ts => (t,i)::rowGates (i+1) ts

lemma fold_rowGates (i : ℕ) (ts : List TileWeights) (f : DiluteState) :
    (rowGates i ts).foldl (fun f g => act g.1 g.2 f) f = planarRow i ts f := by
  induction ts generalizing i f with
  | nil => rfl
  | cons t ts ih => exact ih (i+1) (act t i f)

lemma rowGates_valid {w i : ℕ} (ts : List TileWeights) (h : i+ts.length<w) :
    ∀ g ∈ rowGates i ts, g.2+1<w := by
  induction ts generalizing i with
  | nil => simp [rowGates]
  | cons t ts ih =>
    intro g hg
    simp only [rowGates,List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp at h
      simp only
      omega
    · exact ih (by simp at h; omega) g hg

noncomputable def twoRowGates (n : ℕ) (tsA tsB : List TileWeights) (kR kL : ℂ) :
    List (TileWeights × ℕ) :=
  [(boundaryWeights kR,0)] ++ rowGates 1 tsB ++ rowGates 0 tsA ++ [(boundaryWeights kL,n)]

lemma twoRowGates_valid {n : ℕ} (tsA tsB : List TileWeights)
    (hA : tsA.length=n) (hB : tsB.length=n) (kR kL : ℂ) :
    ∀ g ∈ twoRowGates n tsA tsB kR kL, g.2+1<n+2 := by
  intro g hg
  simp only [twoRowGates,List.mem_append,List.mem_singleton] at hg
  rcases hg with ((rfl | hg) | hg) | rfl
  · simp
  · exact rowGates_valid tsB (by omega : 1+tsB.length<n+2) g hg
  · exact rowGates_valid tsA (by omega : 0+tsA.length<n+2) g hg
  · simp

lemma fold_twoRowGates (n : ℕ) (tsA tsB : List TileWeights) (kR kL : ℂ)
    (f : DiluteState) :
    (twoRowGates n tsA tsB kR kL).foldl (fun f g => act g.1 g.2 f) f =
      act (boundaryWeights kL) n
        (planarRow 0 tsA (planarRow 1 tsB (act (boundaryWeights kR) 0 f))) := by
  simp only [twoRowGates,List.foldl_append,List.foldl_cons,List.foldl_nil,fold_rowGates]

lemma span_zero_of_length {n : ℕ} {f : DiluteState} (hf : PlanarSpan n f)
    (xs : List Spin) (hx : xs.length≠n) : f xs=0 := by
  induction hf with
  | zero => rfl
  | basis o k w hl hc =>
    have hne : occupancy xs≠o := by
      intro he
      have he' := congrArg List.length he
      simp only [occupancy,List.length_map] at he'
      exact hx (he'.trans hl)
    simp [embed,hne]
  | add hf hg ihf ihg => simp [ihf,ihg]
  | smul z hf ihf => simp [ihf]

noncomputable def sourceDoubleRow (n : ℕ) (tsA tsB : List TileWeights) (kR kL : ℂ)
    (f : DiluteState) : DiluteState := fun xs =>
  if xs.length=n then
    ∑ a : Spin, ∑ b : Spin, K kL a b * sourceTwoRows tsA tsB (seedAux kR f) (a::b::xs)
  else 0

theorem sourceDoubleRow_eq_network {n : ℕ} (tsA tsB : List TileWeights)
    (hA : tsA.length=n) (hB : tsB.length=n) (kR kL : ℂ)
    {f : DiluteState} (hf : PlanarSpan n f) :
    sourceDoubleRow n tsA tsB kR kL f = auxNetwork (twoRowGates n tsA tsB kR kL) f := by
  funext xs
  by_cases hx : xs.length=n
  · simp only [sourceDoubleRow,hx,ite_true,auxNetwork,removeAux,fold_twoRowGates,seedAux_eq]
    rw [←hx,act_at]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [boundary_output,two_rows_eq tsA tsB hA hB _ xs hx a b]
  · simp only [sourceDoubleRow,hx,ite_false]
    symm
    exact span_zero_of_length
      (auxNetwork_span _ (twoRowGates_valid tsA tsB hA hB kR kL) hf) xs hx

lemma sourceDoubleRow_span {n : ℕ} (tsA tsB : List TileWeights)
    (hA : tsA.length=n) (hB : tsB.length=n) (kR kL : ℂ)
    {f : DiluteState} (hf : PlanarSpan n f) :
    PlanarSpan n (sourceDoubleRow n tsA tsB kR kL f) := by
  rw [sourceDoubleRow_eq_network tsA tsB hA hB kR kL hf]
  exact auxNetwork_span _ (twoRowGates_valid tsA tsB hA hB kR kL) hf

theorem sourceDoubleRow_vacuum {n : ℕ} (tsA tsB : List TileWeights)
    (hA : tsA.length=n) (hB : tsB.length=n) (kR kL : ℂ)
    {f : DiluteState} (hf : PlanarSpan n f) :
    sourceDoubleRow n tsA tsB kR kL f (List.replicate n none) =
      f (List.replicate n none) := by
  rw [sourceDoubleRow_eq_network tsA tsB hA hB kR kL hf]
  exact auxNetwork_vacuum _ (twoRowGates_valid tsA tsB hA hB kR kL) hf

noncomputable def vacuum (n : ℕ) : DiluteState :=
  embed (List.replicate n false) (fun _ => 1)

lemma vacuum_span (n : ℕ) : PlanarSpan n (vacuum n) := by
  exact .basis _ 0 .start (by simp) (by simp [List.count_replicate])

lemma vacuum_value (n : ℕ) : vacuum n (List.replicate n none) = 1 := by
  simp [vacuum,embed,occupancy]

noncomputable def sourceRows (n : ℕ) (tsA tsB : List TileWeights) (kR kL : ℂ) :
    ℕ → DiluteState
  | 0 => vacuum n
  | m+1 => sourceDoubleRow n tsA tsB kR kL (sourceRows n tsA tsB kR kL m)

lemma sourceRows_span {n : ℕ} (tsA tsB : List TileWeights)
    (hA : tsA.length=n) (hB : tsB.length=n) (kR kL : ℂ) (m : ℕ) :
    PlanarSpan n (sourceRows n tsA tsB kR kL m) := by
  induction m with
  | zero => exact vacuum_span n
  | succ m ih => exact sourceDoubleRow_span tsA tsB hA hB kR kL ih

theorem sourceRows_empty_entry {n : ℕ} (tsA tsB : List TileWeights)
    (hA : tsA.length=n) (hB : tsB.length=n) (kR kL : ℂ) (m : ℕ) :
    sourceRows n tsA tsB kR kL m (List.replicate n none) = 1 := by
  induction m with
  | zero => exact vacuum_value n
  | succ m ih =>
    rw [sourceRows,sourceDoubleRow_vacuum tsA tsB hA hB kR kL
      (sourceRows_span tsA tsB hA hB kR kL m)]
    exact ih

end CriticalHoneycomb.Transfer.PlanarNormalization

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma normalizedR_sourceR (u : ℝ) : normalizedR u=
    Planar.sourceR (Transfer.a u) (Transfer.h u) (Transfer.v u) (Transfer.c u) (Transfer.d u) := by
  rfl
lemma spectralR_charge (u : ℝ) (a b c d : Spin)
    (hz : spectralR u (a,b) (c,d)≠0) : spinCharge a+spinCharge b=spinCharge c+spinCharge d := by
  by_cases hQ : Q u=0
  · simp [spectralR,hQ] at hz
  · rw [spectralR_normalized u hQ,normalizedR_sourceR] at hz
    have h:=sourceR_charge (Transfer.a u) (Transfer.h u) (Transfer.v u)
      (Transfer.c u) (Transfer.d u) b a c d hz
    omega
lemma row_charge (n : ℕ) (R : Fin n→Matrix Pair Pair ℂ)
    (hR : ∀ i a b c d,R i (a,b) (c,d)≠0→spinCharge a+spinCharge b=spinCharge c+spinCharge d)
    (w e : Space n) (a b : Spin) (hz : row n R w e a b≠0) :
    columnCharge w+spinCharge a=columnCharge e+spinCharge b := by
  induction n generalizing a b with
  | zero =>
    have hab : a=b := by
      by_contra hab
      simp [row,hab] at hz
    subst b
    simp [columnCharge]
  | succ n ih =>
    simp only [row,Matrix.mul_apply] at hz
    obtain ⟨z,_,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    have h0:=hR 0 a (w 0) z (e 0) (mul_ne_zero_iff.mp hz).1
    have h1:=ih (Fin.tail R) (fun i=>hR i.succ) (Fin.tail w) (Fin.tail e) z b
      (mul_ne_zero_iff.mp hz).2
    simp only [columnCharge,Fin.sum_univ_succ,Fin.tail] at h0 h1 ⊢
    omega
lemma spectral_row_charge (n : ℕ) (ξ : Fin n→ℝ) (u : ℝ)
    (w e : Space n) (a b : Spin) (hz : row n (exactSites n ξ u) w e a b≠0) :
    columnCharge w+spinCharge a=columnCharge e+spinCharge b :=
  row_charge n _ (fun i=> spectralR_charge (u+ξ i)) w e a b hz
lemma bulkRows_charge (n : ℕ) (ξ : Fin n→ℝ) (u : ℝ)
    (w e : Space n) (p q : Pair) (hz : bulkRows n ξ u w e p q≠0) :
    columnCharge w+(spinCharge p.1+spinCharge p.2)=
      columnCharge e+(spinCharge q.1+spinCharge q.2) := by
  simp only [bulkRows,forward,Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap,Matrix.of_apply] at hz
  obtain ⟨v,_,hv⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
  have h1:=spectral_row_charge n ξ u w v p.1 q.1 (mul_ne_zero_iff.mp hv).1
  have h2:=spectral_row_charge n ξ (b-u) v e p.2 q.2 (mul_ne_zero_iff.mp hv).2
  omega
lemma K0_charge (u : ℝ) (p : Pair) (hz : K0 u p≠0) : spinCharge p.1+spinCharge p.2=0 := by
  rcases p with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> simp_all [K0,boundary0,Fin.rev,spinCharge]
lemma K1_charge (u : ℝ) (p : Pair) (hz : K1 u p≠0) : spinCharge p.1+spinCharge p.2= -1 := by
  rcases p with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> simp_all [K1,boundary1,Fin.rev,spinCharge]
lemma coefficient_shift (n : ℕ) (ξ : Fin n→ℝ) (u : ℝ) (i j : Bool) :
    HasShift (coefficient n ξ u i j) ((if i then 1 else 0)-(if j then 1 else 0)) := by
  intro w e hz
  obtain ⟨p,_,hp⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨q,_,hq⟩:=Finset.exists_ne_zero_of_sum_ne_zero hp
  have hb:=bulkRows_charge n ξ u w e p q (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hq).1).2
  have hL:= (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hq).1).1
  have hR:= (mul_ne_zero_iff.mp hq).2
  cases i <;> cases j <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hL hR ⊢
  · have hl:=K0_charge (b-u) p hL;have hr:=K0_charge u q hR;omega
  · have hl:=K0_charge (b-u) p hL;have hr:=K1_charge u q hR;omega
  · have hl:=K1_charge (b-u) p hL;have hr:=K0_charge u q hR;omega
  · have hl:=K1_charge (b-u) p hL;have hr:=K1_charge u q hR;omega
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma spinCharge_rev (a : Spin) : spinCharge a.rev= -spinCharge a := by
  fin_cases a <;> norm_num [spinCharge,Fin.rev]
lemma columnCharge_reflected (n : ℕ) (w : Space n) :
    columnCharge (reflectedSites n w)= -columnCharge w := by
  change (∑ i : Fin n,spinCharge ((w i.rev).rev))= -∑ i : Fin n,spinCharge (w i)
  simp only [spinCharge_rev,Finset.sum_neg_distrib]
  exact congrArg Neg.neg (Equiv.sum_comp (Fin.revPerm) (fun i : Fin n=>spinCharge (w i)))
lemma physical_base (n : ℕ) (u : ℝ) (w e : Space n) :
    base (physicalFamily n u w e)=
      star (coefficient n (homogeneous n) u false false (reflectedSites n w) (reflectedSites n e)) := by
  change base (reflected (T n (homogeneous n) u (reflectedSites n w) (reflectedSites n e)))=_
  rw [reflected_base,T_coefficients,base_form]
lemma physical_left (n : ℕ) (u : ℝ) (w e : Space n) :
    left (physicalFamily n u w e)=
      star (coefficient n (homogeneous n) u false true (reflectedSites n w) (reflectedSites n e)) := by
  change left (reflected (T n (homogeneous n) u (reflectedSites n w) (reflectedSites n e)))=_
  rw [reflected_left,T_coefficients,right_form]
lemma physical_right (n : ℕ) (u : ℝ) (w e : Space n) :
    right (physicalFamily n u w e)=
      star (coefficient n (homogeneous n) u true false (reflectedSites n w) (reflectedSites n e)) := by
  change right (reflected (T n (homogeneous n) u (reflectedSites n w) (reflectedSites n e)))=_
  rw [reflected_right,T_coefficients,left_form]
lemma physical_left_shift (n : ℕ) (u : ℝ) :
    HasShift (fun w e=>left (physicalFamily n u w e)) 1 := by
  intro w e hz
  change left (physicalFamily n u w e)≠0 at hz
  rw [physical_left,star_ne_zero] at hz
  have h:=coefficient_shift n (homogeneous n) u false true (reflectedSites n w) (reflectedSites n e) hz
  simp only [Bool.false_eq_true,ite_false,ite_true,columnCharge_reflected] at h
  omega
lemma physical_right_shift (n : ℕ) (u : ℝ) :
    HasShift (fun w e=>right (physicalFamily n u w e)) (-1) := by
  intro w e hz
  change right (physicalFamily n u w e)≠0 at hz
  rw [physical_right,star_ne_zero] at hz
  have h:=coefficient_shift n (homogeneous n) u true false (reflectedSites n w) (reflectedSites n e) hz
  simp only [Bool.false_eq_true,ite_false,ite_true,columnCharge_reflected] at h
  omega
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
noncomputable def spectralWeights (u : ℝ) : PlanarNormalization.TileWeights :=
  ⟨Transfer.a u,Transfer.h u,Transfer.v u,Transfer.c u,Transfer.d u⟩
lemma spectralR_weights (u : ℝ) (hu : Q u≠0) : spectralR u=
    PlanarNormalization.sourceR (spectralWeights u) := by
  rw [spectralR_normalized u hu,normalizedR_sourceR]
  rfl
lemma row_planar_kernel (t : PlanarNormalization.TileWeights) (n : ℕ)
    (w e : Fin n→PlanarNormalization.Spin) (a b : PlanarNormalization.Spin) :
    row n (fun _=>PlanarNormalization.sourceR t)
      (reverseSites n (columnSpinEquiv n w)) (reverseSites n (columnSpinEquiv n e))
      (spinEquiv a) (spinEquiv b)=PlanarNormalization.columnKernelSpin t n b a w e := by
  rw [row_eq_matrixPath n (fun _=>PlanarNormalization.sourceR t)]
  unfold matrixPath
  rw [←(reverseSites n).sum_comp,←(columnSpinEquiv n).sum_comp]
  unfold PlanarNormalization.columnKernelSpin
  apply Finset.sum_congr rfl
  intro v hv
  simp only [cons_reverseSites,Fin.rev_last,reverseSites_apply]
  have he : Fin.snoc (α:=fun _=>Spin) (columnSpinEquiv n v) (spinEquiv a)=
      fun i=>spinEquiv (Fin.snoc (α:=fun _=>PlanarNormalization.Spin) v a i) := by
    funext i
    refine Fin.lastCases ?_ (fun j=>?_) i <;> simp
  simp only [he,Equiv.apply_eq_iff_eq]
  split_ifs with h
  · rw [←Equiv.prod_comp (Fin.revPerm (n:=n))]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Fin.revPerm_apply,Fin.rev_rev,Fin.rev_castSucc,block,columnSpinEquiv_apply]
    exact (PlanarNormalization.tile_eq_sourceR _ _ _ _ _).symm
  · rfl
lemma spectral_row_planar_kernel (u : ℝ) (hu : Q u≠0) (n : ℕ)
    (w e : Fin n→PlanarNormalization.Spin) (a b : PlanarNormalization.Spin) :
    row n (fun _=>spectralR u)
      (reverseSites n (columnSpinEquiv n w)) (reverseSites n (columnSpinEquiv n e))
      (spinEquiv a) (spinEquiv b)=PlanarNormalization.columnKernelSpin (spectralWeights u) n b a w e := by
  rw [spectralR_weights u hu]
  exact row_planar_kernel _ _ _ _ _ _
noncomputable def boundaryWeight (u : ℝ) : ℂ := sine (gamma-u)/sine (gamma+u)
lemma K0_planar (u : ℝ) (a b : PlanarNormalization.Spin) :
    K0 u (spinEquiv a,spinEquiv b)=PlanarNormalization.K (boundaryWeight u) a b := by
  fin_cases a <;> fin_cases b <;>
    simp [K0,boundary0,spinEquiv,PlanarNormalization.spinIndex,Fin.rev,spinValue,
      PlanarNormalization.K,PlanarNormalization.cup,boundaryWeight,Reflection.phase,
      PlanarNormalization.phase,point,mul_comm]
lemma K0_spin_star (u : ℝ) (a b : Spin) :
    K0 u (a.rev,b.rev)=star (K0 u (a,b)) := by
  fin_cases a <;> fin_cases b <;>
    simp [K0,boundary0,Fin.rev,spinValue,Fusion.phase_star,Fusion.sine_star]
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma bulkRows_spin_star (n : ℕ) (u : ℝ) (w e : Space n) (a b c d : Spin) :
    bulkRows n (homogeneous n) u (flipSites n w) (flipSites n e) (a.rev,b.rev) (c.rev,d.rev)=
      star (bulkRows n (homogeneous n) u w e (a,b) (c,d)) := by
  simp only [bulkRows,forward,Matrix.sum_apply,Matrix.kronecker,
    Matrix.kroneckerMap,Matrix.of_apply,star_sum]
  rw [←Equiv.sum_comp (flipSites n)]
  apply Finset.sum_congr rfl
  intro v hv
  change row n (fun _=>spectralR (u+-L/2)) (flipSites n w) (flipSites n v) a.rev c.rev *
    row n (fun _=>spectralR ((Reflection.b-u)+-L/2)) (flipSites n v)
      (flipSites n e) b.rev d.rev = _
  rw [row_spin_star,row_spin_star,star_mul]
  exact mul_comm _ _
lemma coefficient_base_spin_star (n : ℕ) (u : ℝ) (w e : Space n) :
    coefficient n (homogeneous n) u false false (flipSites n w) (flipSites n e)=
      star (coefficient n (homogeneous n) u false false w e) := by
  simp only [coefficient,Bool.false_eq_true,ite_false,star_sum]
  rw [←Equiv.sum_comp (Equiv.prodCongr Fusion.spinFlip Fusion.spinFlip)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←Equiv.sum_comp (Equiv.prodCongr Fusion.spinFlip Fusion.spinFlip)]
  apply Finset.sum_congr rfl
  intro q hq
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  simp only [Equiv.prodCongr_apply,Prod.map_apply,Fusion.spinFlip_apply,K0_spin_star,
    bulkRows_spin_star,star_mul]
  ring
lemma physical_base_reversed (n : ℕ) (u : ℝ) (w e : Space n) :
    base (physicalFamily n u w e)=
      coefficient n (homogeneous n) u false false (reverseSites n w) (reverseSites n e) := by
  rw [physical_base]
  have h : ∀ x : Space n, reflectedSites n x=flipSites n (reverseSites n x) := fun x=>rfl
  rw [h,h,coefficient_base_spin_star,star_star]
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators
lemma planarRow_sum {α : Type*} (s : Finset α) (i : ℕ) (ts : List TileWeights)
    (f : α→DiluteState) : planarRow i ts (∑ a∈s,f a)=∑ a∈s,planarRow i ts (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change planarRow i ts (fun _=>0)=fun _=>0
    exact planarRow_zero i ts
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    change planarRow i ts (fun xs=>f a xs+(∑ a∈s,f a) xs)=_
    rw [planarRow_add,ih]
    rfl
lemma seedAux_sum (k : ℂ) (f : DiluteState) : seedAux k f=
    ∑ a : Spin,∑ b : Spin,(fun xs=> K k a b*fixedSeed a (fixedSeed b f) xs) := by
  funext xs
  cases xs with
  | nil => simp [seedAux,fixedSeed]
  | cons a xs => cases xs with
    | nil => simp [seedAux,fixedSeed]
    | cons b xs => simp only [seedAux,Finset.sum_apply,fixedSeed]; simp
lemma fixed_double_columns_distinct (tA tB : TileWeights) (n : ℕ) (f : DiluteState)
    (s₁ s₂ z₁ z₂ : Spin) (xs : List Spin) (hx : xs.length=n) :
    sourceTwoRows (List.replicate n tA) (List.replicate n tB)
      (fixedSeed s₁ (fixedSeed s₂ f)) (z₁::z₂::xs)=
      fixedColumn tA n s₁ z₁ (fixedColumn tB n s₂ z₂ f) xs := by
  rw [←two_rows_eq (List.replicate n tA) (List.replicate n tB) (by simp) (by simp) _ xs hx z₁ z₂]
  rw [show xs++[z₁,z₂]=(xs++[z₁])++[z₂] by simp]
  rw [planarRow_suffix 0 _ _ (xs++[z₁]) [z₂] (by simp [hx])]
  unfold fixedColumn
  apply planarRow_congr_of_length 0 (n+1) _ _ _ _ _ (by simp [hx])
  intro ys hy
  cases ys with
  | nil => simp at hy
  | cons a ys =>
    simp only [List.cons_append,planarRow_under,fixedSeed]
    by_cases ha : a=s₁
    · subst a
      simp only [ite_true]
      rfl
    · simp only [ha,ite_false]
      exact congrFun (planarRow_zero 0 (List.replicate n tB)) (ys++[z₂])
lemma sourceDoubleRow_fixed (tA tB : TileWeights) (n : ℕ) (kR kL : ℂ)
    (f : DiluteState) (xs : List Spin) (hx : xs.length=n) :
    sourceDoubleRow n (List.replicate n tA) (List.replicate n tB) kR kL f xs=
      ∑ a : Spin,∑ b : Spin,∑ c : Spin,∑ d : Spin,
        K kL a b*K kR c d*fixedColumn tA n c a (fixedColumn tB n d b f) xs := by
  simp only [sourceDoubleRow,hx,ite_true]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [←two_rows_eq (List.replicate n tA) (List.replicate n tB) (by simp) (by simp) _ xs hx a b,
    seedAux_sum]
  simp only [planarRow_sum,planarRow_smul,Finset.sum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_assoc,two_rows_eq (List.replicate n tA) (List.replicate n tB) (by simp) (by simp) _ xs hx a b,
    fixed_double_columns_distinct _ _ _ _ _ _ _ _ _ hx]
end CriticalHoneycomb.Transfer.PlanarNormalization

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
noncomputable def modelKernel (t : PlanarNormalization.TileWeights) (n : ℕ)
    (a b : PlanarNormalization.Spin) : Matrix (Space n) (Space n) ℂ :=
  fun w e=>PlanarNormalization.columnKernelSpin t n a b
    ((columnSpinEquiv n).symm w) ((columnSpinEquiv n).symm e)
lemma modelKernel_mulVec (t : PlanarNormalization.TileWeights) (n : ℕ)
    (a b : PlanarNormalization.Spin) (f : PlanarNormalization.DiluteState) :
    modelKernel t n a b*ᵥcolumnVector n f=
      columnVector n (PlanarNormalization.fixedColumn t n a b f) := by
  funext w
  obtain ⟨w,rfl⟩:=(columnSpinEquiv n).surjective w
  simp only [columnVector,columnSpinEquiv_apply,Equiv.symm_apply_apply]
  rw [PlanarNormalization.fixedColumn_eq_kernel]
  simp only [Matrix.mulVec,dotProduct]
  rw [←(columnSpinEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro e he
  simp only [modelKernel,Equiv.symm_apply_apply,columnVector,columnSpinEquiv_apply]
lemma spectral_row_modelKernel (u : ℝ) (hu : Q u≠0) (n : ℕ)
    (w e : Space n) (a b : PlanarNormalization.Spin) :
    row n (fun _=>spectralR u) (reverseSites n w) (reverseSites n e) (spinEquiv a) (spinEquiv b)=
      modelKernel (spectralWeights u) n b a w e := by
  obtain ⟨w,rfl⟩:=(columnSpinEquiv n).surjective w
  obtain ⟨e,rfl⟩:=(columnSpinEquiv n).surjective e
  rw [spectral_row_planar_kernel u hu]
  simp only [modelKernel,Equiv.symm_apply_apply]
lemma bulkRows_modelKernel (n : ℕ) (u : ℝ)
    (h1 : Q (u-L/2)≠0) (h2 : Q (b-u-L/2)≠0) (w e : Space n)
    (a b' c d : PlanarNormalization.Spin) :
    bulkRows n (homogeneous n) u (reverseSites n w) (reverseSites n e)
      (spinEquiv a,spinEquiv b') (spinEquiv c,spinEquiv d)=
      (modelKernel (spectralWeights (u-L/2)) n c a*
       modelKernel (spectralWeights (b-u-L/2)) n d b') w e := by
  simp only [bulkRows,forward,Matrix.sum_apply,Matrix.kronecker,
    Matrix.kroneckerMap,Matrix.of_apply,Matrix.mul_apply]
  rw [←Equiv.sum_comp (reverseSites n)]
  apply Finset.sum_congr rfl
  intro v hv
  have hs : ∀ t : ℝ,exactSites n (homogeneous n) t=fun _=>spectralR (t-L/2) := by
    intro t
    funext i
    change spectralR (t+-L/2)=spectralR (t-L/2)
    congr 1
    ring
  rw [hs,hs,spectral_row_modelKernel _ h1,spectral_row_modelKernel _ h2]
lemma physical_base_matrix (n : ℕ) (u : ℝ)
    (h1 : Q (u-L/2)≠0) (h2 : Q (b-u-L/2)≠0) :
    (physicalFamily n u).map jetBaseHom=
      ∑ a : PlanarNormalization.Spin,∑ b' : PlanarNormalization.Spin,
      ∑ c : PlanarNormalization.Spin,∑ d : PlanarNormalization.Spin,
        (PlanarNormalization.K (boundaryWeight (b-u)) a b'*
          PlanarNormalization.K (boundaryWeight u) c d) •
        (modelKernel (spectralWeights (u-L/2)) n c a*
          modelKernel (spectralWeights (b-u-L/2)) n d b') := by
  funext w e
  change base (physicalFamily n u w e)=_
  simp only [physical_base_reversed,coefficient,Bool.false_eq_true,ite_false,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fintype.sum_prod_type]
  simp only [←Equiv.sum_comp spinEquiv]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b' hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  rw [K0_planar,K0_planar,bulkRows_modelKernel n u h1 h2]
  ring
lemma physical_base_source (n : ℕ) (u : ℝ)
    (h1 : Q (u-L/2)≠0) (h2 : Q (b-u-L/2)≠0)
    (f : PlanarNormalization.DiluteState) :
    (physicalFamily n u).map jetBaseHom*ᵥcolumnVector n f=
      columnVector n (PlanarNormalization.sourceDoubleRow n
        (List.replicate n (spectralWeights (u-L/2)))
        (List.replicate n (spectralWeights (b-u-L/2)))
        (boundaryWeight u) (boundaryWeight (b-u)) f) := by
  rw [physical_base_matrix n u h1 h2]
  simp only [Matrix.sum_mulVec,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,modelKernel_mulVec]
  funext w
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,columnVector,
    PlanarNormalization.sourceDoubleRow_fixed _ _ _ _ _ _ _ (List.length_ofFn)]
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open BoundaryJet Filter Topology
open scoped Matrix
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma commute_archProjection (W : ℕ) (M : Matrix (Column (W+1)) (Column (W+1)) ℂ)
    (hM : Commute M (physicalDoubleMatrix (W+1))) : Commute M (archProjection W) := by
  have hL := (tendsto_const_nhds (x:=M)).mul (physical_double_rank_one W)
  have hR := (physical_double_rank_one W).mul (tendsto_const_nhds (x:=M))
  apply tendsto_nhds_unique hL
  exact hR.congr (fun n=>(hM.pow_right n).eq.symm)
lemma base_commute (W : ℕ) (M : Matrix (Column (W+1)) (Column (W+1)) Jet)
    (hM : Commute (markedDoubleMatrix (W+1)) M) :
    Commute (M.map jetBaseHom) (physicalDoubleMatrix (W+1)) := by
  have h:=congrArg jetBaseHom.mapMatrix hM.symm.eq
  change Commute (jetBaseHom.mapMatrix M) (physicalDoubleMatrix (W+1))
  change _*_= _*_
  simpa only [map_mul,show jetBaseHom.mapMatrix (markedDoubleMatrix (W+1))=physicalDoubleMatrix (W+1) from marked_base (W+1)] using h
lemma base_common_line (W : ℕ) (M : Matrix (Column (W+1)) (Column (W+1)) Jet)
    (hM : Commute (markedDoubleMatrix (W+1)) M) :
    (M.map jetBaseHom)*ᵥarchColumn W=base (commonScalar W M)•archColumn W := by
  have h:=commuting_common_line W M hM
  funext s
  have h':=congrArg base (congrFun h s)
  simpa only [Matrix.mulVec,dotProduct,base_sum,base_mul,markedEigenvector,base_form,
    Matrix.map_apply,jetBaseHom_apply,Pi.smul_apply,smul_eq_mul] using h'
lemma base_common_dual (W : ℕ) (M : Matrix (Column (W+1)) (Column (W+1)) Jet)
    (hM : Commute (markedDoubleMatrix (W+1)) M) (v : Column (W+1)→ℂ) :
    archDual W ((M.map jetBaseHom)*ᵥv)=base (commonScalar W M)*archDual W v := by
  have hp:=commute_archProjection W (M.map jetBaseHom) (base_commute W M hM)
  have h:=congrArg (fun A=>A*ᵥv) hp.eq
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,projection_mulVec,Matrix.mulVec_smul,
    base_common_line W M hM,projection_mulVec] at h
  have h':=congrFun h (fun _=>1)
  simpa only [Pi.smul_apply,smul_eq_mul,archColumn_vacuum,mul_one,one_mul,archDual,mul_comm] using h'.symm
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.PlanarNormalization
lemma vacuumIterate_span (t : TileWeights) (n m : ℕ) :
    PlanarSpan n (((vacuumColumn t n)^[m]) (vacuum n)) := by
  induction m with
  | zero => exact vacuum_span n
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact vacuumColumn_span t ih
end CriticalHoneycomb.Transfer.PlanarNormalization
namespace CriticalHoneycomb.Transfer.RasterGrid
open PlanarNormalization Filter Topology
open scoped Matrix BigOperators
lemma columnVector_at_vacuum (n : ℕ) (f : DiluteState) :
    columnVector n f (fun _=>1)=f (List.replicate n none) := by
  simp [columnVector,spinEquiv]
lemma columnVector_physical_iterate (n m : ℕ) (w : Column n) :
    columnVector n (((vacuumColumn physicalWeights n)^[m]) (vacuum n)) w=
      (rowTransfer n^m) w (fun _=>1) := by
  have h:=congrFun (column_pow_mulVec n m (vacuum n)) w
  rw [show columnVector n (vacuum n)=fun east=>if east=(fun _=>1) then 1 else 0 from vector_vacuum n] at h
  simpa only [Matrix.mulVec,dotProduct,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,rowTransfer] using h.symm
lemma physical_iterate_limit (W : ℕ) :
    Tendsto (fun m=>columnVector (W+1)
      (((vacuumColumn physicalWeights (W+1))^[m]) (vacuum (W+1))))
      atTop (𝓝 (archColumn W)) := by
  apply tendsto_pi_nhds.mpr
  intro w
  simpa only [columnVector_physical_iterate] using archColumn_limit W w
end CriticalHoneycomb.Transfer.RasterGrid
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid PlanarNormalization Filter Topology
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma physical_base_on_vacuumIterate (n m : ℕ) (u : ℝ)
    (h1 : Q (u-L/2)≠0) (h2 : Q (b-u-L/2)≠0) :
    ((physicalFamily n u).map jetBaseHom*ᵥcolumnVector n
      (((vacuumColumn physicalWeights n)^[m]) (vacuum n))) (fun _=>1)=1 := by
  rw [physical_base_source n u h1 h2,columnVector_at_vacuum,
    sourceDoubleRow_vacuum _ _ (by simp) (by simp) _ _
      (vacuumIterate_span physicalWeights n m)]
  exact vacuumRectangle physicalWeights n m
lemma physical_base_archColumn (W : ℕ) (u : ℝ)
    (h1 : Q (u-L/2)≠0) (h2 : Q (b-u-L/2)≠0) :
    ((physicalFamily (W+1) u).map jetBaseHom*ᵥarchColumn W) (fun _=>1)=1 := by
  have hc : Continuous (fun v : Column (W+1)→ℂ =>
      (physicalFamily (W+1) u).map jetBaseHom*ᵥv) :=
    continuous_const.matrix_mulVec continuous_id
  have hlim := hc.continuousAt.tendsto.comp (physical_iterate_limit W)
  have hv := (tendsto_pi_nhds.mp hlim) (fun _=>1)
  apply tendsto_nhds_unique hv
  exact tendsto_const_nhds.congr (fun m=>(physical_base_on_vacuumIterate (W+1) m u h1 h2).symm)
theorem physicalScalar_base (W : ℕ) (u : ℝ)
    (hu : Nonsingular (W+1) (homogeneous (W+1)) u) :
    base (physicalScalar W u)=1 := by
  have hM : Commute (markedDoubleMatrix (W+1)) (physicalFamily (W+1) u) := by
    rw [←physicalFamily_at_gamma]
    exact physicalFamily_commute _ gamma u (homogeneous_nonsingular _) hu
  have h := congrFun (base_common_line W (physicalFamily (W+1) u) hM) (fun _=>1)
  have h1 : Q (u-L/2)≠0 := by simpa only [homogeneous,sub_eq_add_neg,neg_div] using (hu.2.2 ⟨0,by omega⟩).1
  have h2 : Q (b-u-L/2)≠0 := by simpa only [homogeneous,sub_eq_add_neg,neg_div] using (hu.2.2 ⟨0,by omega⟩).2
  rw [physical_base_archColumn W u h1 h2] at h
  simpa only [Pi.smul_apply,smul_eq_mul,archColumn_vacuum,mul_one,physicalScalar] using h.symm
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open BoundaryJet
open scoped Matrix
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma common_scalar_left_zero (W : ℕ) (M : Matrix (Column (W+1)) (Column (W+1)) Jet)
    (hM : Commute (markedDoubleMatrix (W+1)) M)
    {q : ℤ} (hshift : HasShift (fun w e=>left (M w e)) q) (hq : q≠0) :
    left (commonScalar W M)=0 := by
  have h:=commuting_common_line W M hM
  have he : (M.map jetBaseHom)*ᵥeigenLeft W+(fun w e=>left (M w e))*ᵥarchColumn W=
      base (commonScalar W M)•eigenLeft W+left (commonScalar W M)•archColumn W := by
    funext s
    have hs:=congrArg left (congrFun h s)
    simpa only [Matrix.mulVec,dotProduct,left_sum,left_mul,markedEigenvector,base_form,left_form,
      Matrix.map_apply,jetBaseHom_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib] using hs
  have hz:=projection_shift_zero hshift hq
  have hd:=congrArg (archDual W) he
  change archDual W _=0 at hz
  rw [archDual_add,archDual_add,base_common_dual W M hM,archDual_smul,archDual_smul,archDual_A,
    hz,mul_one,add_zero] at hd
  exact (add_eq_left.mp hd.symm)
lemma common_scalar_right_zero (W : ℕ) (M : Matrix (Column (W+1)) (Column (W+1)) Jet)
    (hM : Commute (markedDoubleMatrix (W+1)) M)
    {q : ℤ} (hshift : HasShift (fun w e=>right (M w e)) q) (hq : q≠0) :
    right (commonScalar W M)=0 := by
  have h:=commuting_common_line W M hM
  have he : (M.map jetBaseHom)*ᵥeigenRight W+(fun w e=>right (M w e))*ᵥarchColumn W=
      base (commonScalar W M)•eigenRight W+right (commonScalar W M)•archColumn W := by
    funext s
    have hs:=congrArg right (congrFun h s)
    simpa only [Matrix.mulVec,dotProduct,right_sum,right_mul,markedEigenvector,base_form,right_form,
      Matrix.map_apply,jetBaseHom_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib] using hs
  have hz:=projection_shift_zero hshift hq
  have hd:=congrArg (archDual W) he
  change archDual W _=0 at hz
  rw [archDual_add,archDual_add,base_common_dual W M hM,archDual_smul,archDual_smul,archDual_A,
    hz,mul_one,add_zero] at hd
  exact (add_eq_left.mp hd.symm)
end CriticalHoneycomb.Transfer.RasterGrid
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
lemma physicalScalar_singles (W : ℕ) (u : ℝ)
    (hu : Nonsingular (W+1) (homogeneous (W+1)) u) :
    left (physicalScalar W u)=0 ∧ right (physicalScalar W u)=0 := by
  have hc : Commute (markedDoubleMatrix (W+1)) (physicalFamily (W+1) u) := by
    rw [←physicalFamily_at_gamma]
    exact physicalFamily_commute (W+1) gamma u (homogeneous_nonsingular _) hu
  exact ⟨common_scalar_left_zero W _ hc (physical_left_shift (W+1) u) (by norm_num),
    common_scalar_right_zero W _ hc (physical_right_shift (W+1) u) (by norm_num)⟩
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
local instance : SMulCommClass Jet Jet Jet where
  smul_comm a b c := by simp only [smul_eq_mul];ring
lemma physicalScalar_form (W : ℕ) (u : ℝ)
    (hu : Nonsingular (W+1) (homogeneous (W+1)) u) :
    physicalScalar W u=form 1 0 0 (both (physicalScalar W u)) := by
  apply jet_ext
  · simpa only [base_form] using physicalScalar_base W u hu
  · simpa only [left_form] using (physicalScalar_singles W u hu).1
  · simpa only [right_form] using (physicalScalar_singles W u hu).2
  · simp only [both_form]
lemma sine_ne_zero_interval {x : ℝ} (h0 : 0<x) (hp : x<Real.pi) : sine x≠0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h0 hp))
lemma homogeneous_nonsingular_interval (n : ℕ) {t : ℝ}
    (h0 : -gamma<t) (hp : t<b+gamma) : Nonsingular n (homogeneous n) t := by
  have hπ:=Real.pi_pos
  simp only [gamma,b] at h0 hp
  have hsin : ∀ x : ℝ,0<x→x<Real.pi→sine x≠0 := fun x h1 h2=>sine_ne_zero_interval h1 h2
  refine ⟨?_,?_,fun i=>⟨?_,?_⟩⟩
  · apply hsin <;> simp only [gamma] <;> linarith
  · apply hsin <;> simp only [gamma,b] <;> linarith
  · apply mul_ne_zero <;> apply hsin <;> simp only [homogeneous,L,b] <;> linarith
  · apply mul_ne_zero <;> apply hsin <;> simp only [homogeneous,L,b] <;> linarith
lemma physicalFamily_node_fusion (n : ℕ) (i : Fin n) (t : ℝ)
    (ht : t=L-homogeneous n i ∨ t=L+homogeneous n i)
    (hm : Nonsingular n (homogeneous n) (t-L))
    (hp : Nonsingular n (homogeneous n) (t+L))
    (hc : Nonsingular n (homogeneous n) t) :
    physicalFamily n (t-L)*physicalFamily n (t+L)=physicalFamily n t := by
  have h:=congrArg (reorient n) (source_global_spectral_fusion n (homogeneous n) i t ht hm hp hc)
  change reorient n (T n (homogeneous n) (t-L))*reorient n (T n (homogeneous n) (t+L))=
    reorient n (T n (homogeneous n) t)
  simpa only [reorient_mul] using h
lemma commonScalar_mul_line (W : ℕ) (M N : Matrix (Column (W+1)) (Column (W+1)) Jet)
    (hN : N*ᵥmarkedEigenvector W=commonScalar W N•markedEigenvector W) :
    commonScalar W (M*N)=commonScalar W M*commonScalar W N := by
  change normalizedDual W ⬝ᵥ ((M*N)*ᵥmarkedEigenvector W)=_
  rw [←Matrix.mulVec_mulVec,hN,Matrix.mulVec_smul,dotProduct_smul]
  change commonScalar W N*commonScalar W M=commonScalar W M*commonScalar W N
  exact mul_comm (commonScalar W N) (commonScalar W M)
lemma both_mul_normalized (a c : Jet) (ha : base a=1) (hc : base c=1)
    (hl : left a=0) (hr : right a=0) : both (a*c)=both a+both c := by
  rw [both_mul,ha,hc,hl,hr]
  simp only [one_mul,mul_one,zero_mul,add_zero]
  exact add_comm _ _
lemma physicalScalar_node_fusion (W : ℕ) (i : Fin (W+1)) (t : ℝ)
    (ht : t=L-homogeneous (W+1) i ∨ t=L+homogeneous (W+1) i)
    (hm : Nonsingular (W+1) (homogeneous (W+1)) (t-L))
    (hp : Nonsingular (W+1) (homogeneous (W+1)) (t+L))
    (hc : Nonsingular (W+1) (homogeneous (W+1)) t) :
    both (physicalScalar W (t-L))+both (physicalScalar W (t+L))=
      both (physicalScalar W t) := by
  have h:=congrArg (commonScalar W) (physicalFamily_node_fusion (W+1) i t ht hm hp hc)
  rw [commonScalar_mul_line W _ _ (physical_common_line W (t+L) hp)] at h
  change physicalScalar W (t-L)*physicalScalar W (t+L)=physicalScalar W t at h
  calc
    _=both (physicalScalar W (t-L)*physicalScalar W (t+L)) :=
      (both_mul_normalized _ _ (physicalScalar_base W (t-L) hm)
        (physicalScalar_base W (t+L) hp) (physicalScalar_singles W (t-L) hm).1
        (physicalScalar_singles W (t-L) hm).2).symm
    _=_ := congrArg both h
noncomputable def physicalP (W : ℕ) (u : ℝ) : ℂ := both (physicalScalar W (gamma+u))
lemma physicalP_reflection (W : ℕ) {u : ℝ}
    (hu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+u)) :
    physicalP W (-u)=physicalP W u := by
  unfold physicalP
  have h : gamma+-u=b-(gamma+u) := by simp only [gamma,b];ring
  rw [h,physicalScalar_reflection W _ hu]
lemma physicalP_mass (W : ℕ) :
    physicalP W 0=2*((∑' γ : StrictBridge (W+1),kappa^γ.val.length):ℝ) := by
  simpa only [physicalP,add_zero] using physicalScalar_mass W
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet
open scoped Matrix BigOperators
lemma K0_at_zero : K0 0=cap := by
  have hs : sine gamma≠0 := sine_ne_zero_interval (by unfold gamma;positivity)
    (by unfold gamma;linarith [Real.pi_pos])
  funext ⟨a,c⟩
  fin_cases a <;> fin_cases c <;>
    simp [K0,boundary0,cap,Fin.rev,hs,spinValue]
lemma K1_at_zero : K1 0=0 := by
  funext p
  simp [K1,boundary1,sine]
lemma K1_at_halfpi : K1 (Real.pi/2)=0 := by
  have hs : sine (2*(Real.pi/2))=0 := by rw [show 2*(Real.pi/2)=Real.pi by ring];simp [sine]
  funext p
  simp only [K1,boundary1,hs]
  split_ifs <;> simp
lemma boundary_ratio_halfpi : sine (gamma-Real.pi/2)/sine (gamma+Real.pi/2)= -1 := by
  have hn : sine (gamma+Real.pi/2)≠0 := sine_ne_zero_interval
    (by unfold gamma;positivity) (by unfold gamma;linarith [Real.pi_pos])
  have he : sine (gamma-Real.pi/2)= -sine (gamma+Real.pi/2) := by
    simpa only [show gamma-Real.pi/2+Real.pi=gamma+Real.pi/2 by ring,neg_neg] using
      (congrArg Neg.neg (sine_add_pi (gamma-Real.pi/2))).symm
  rw [he,neg_div,div_self hn]
lemma K0_at_halfpi : K0 (Real.pi/2)=fun p=> -(parity p.1*cap p) := by
  funext ⟨a,c⟩
  fin_cases a <;> fin_cases c <;>
    simp [K0,boundary0,cap,parity,Fin.rev,spinValue,boundary_ratio_halfpi]
lemma phase_cap_cancel : Reflection.phase*Reflection.phase+
    Reflection.phase⁻¹*Reflection.phase⁻¹=0 := by
  rw [←pow_two,←pow_two,inv_pow,phase_eq,←pow_mul,show 4*2=8 by rfl,root_eight]
  simp
lemma K0_close_cap (u : ℝ) : (∑ p,K0 u p*cap p)=1 := by
  rw [sum_cap]
  simp only [Fin.sum_univ_succ,K0,boundary0,Fin.rev_rev,spinValue]
  norm_num [Fin.rev]
  linear_combination (sine (gamma-u)/sine (gamma+u))*phase_cap_cancel
lemma K1_close_cap (u : ℝ) : (∑ p,K1 u p*cap p)=0 := by
  rw [sum_cap]
  simp [Fin.sum_univ_succ,K1,boundary1,Fin.rev_rev,spinValue]
lemma K0_close_twisted_cap (u : ℝ) : (∑ p,K0 u p* -(parity p.1*cap p))=1 := by
  have he : (∑ p,K0 u p* -(parity p.1*cap p))=
      ∑ a : Spin,K0 u (a,a.rev)* -(parity a*Reflection.phase^(spinValue a)) := by
    rw [Fintype.sum_prod_type]
    simp [cap,mul_ite]
  rw [he]
  simp only [Fin.sum_univ_succ,K0,boundary0,Fin.rev_rev,parity,spinValue]
  norm_num [Fin.rev]
  linear_combination -(sine (gamma-u)/sine (gamma+u))*phase_cap_cancel
lemma K1_close_twisted_cap (u : ℝ) : (∑ p,K1 u p* -(parity p.1*cap p))=0 := by
  rw [Fintype.sum_prod_type]
  simp [cap,mul_ite,Fin.sum_univ_succ,K1,boundary1,parity,spinValue,Fin.rev]
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma forward_cap_all (n : ℕ) (A B : Fin n→Local) (v : Pair→ℂ)
    (h : ∀ i s t,localForward (A i) (B i) s t*ᵥv=if s=t then v else 0)
    (s t : Space n) : forward n A B s t*ᵥv=if s=t then v else 0 := by
  induction n with
  | zero => simp [forward,row,Subsingleton.elim s t]
  | succ n ih =>
    rw [forward_succ,←Matrix.mulVec_mulVec,ih (Fin.tail A) (Fin.tail B) (fun i=>h i.succ)]
    have he : s=t ↔ s 0=t 0 ∧ Fin.tail s=Fin.tail t := by
      constructor
      · intro h;subst t;exact ⟨rfl,rfl⟩
      · rintro ⟨hh,ht⟩
        rw [←Fin.cons_self_tail s,←Fin.cons_self_tail t,hh,ht]
    by_cases ht : Fin.tail s=Fin.tail t
    · rw [ite_eq_left ht,h 0]
      simp only [he,ht,and_true]
    · rw [ite_eq_right ht,Matrix.mulVec_zero]
      simp only [he,ht,and_false,ite_false]
lemma closed_at_cap (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) (v : Pair→ℂ)
    (hr : K1 u=0) (h0 : K0 u=v)
    (hbulk : ∀ s t,bulkRows N ξ u s t*ᵥv=if s=t then v else 0)
    (hc0 : ∑ p,K0 (b-u) p*v p=1) (hc1 : ∑ p,K1 (b-u) p*v p=0) :
    T N ξ u=1 := by
  funext s t
  rw [T_coefficients]
  have coeff (i : Bool) : coefficient N ξ u i false s t=if s=t then if i then 0 else 1 else 0 := by
    unfold coefficient
    simp only [Bool.false_eq_true,ite_false]
    have he : (∑ p,∑ q,(if i=true then K1 (b-u) p else K0 (b-u) p)*
        bulkRows N ξ u s t p q*K0 u q)=
        ∑ p,(if i=true then K1 (b-u) p else K0 (b-u) p)*(bulkRows N ξ u s t*ᵥv) p := by
      simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,h0,mul_assoc]
    rw [he,hbulk]
    by_cases hs : s=t
    · simp only [ite_eq_left hs]
      cases i
      · simpa only [Bool.false_eq_true,ite_false] using hc0
      · simpa only [ite_true] using hc1
    · simp [hs]
  have coeffR (i : Bool) : coefficient N ξ u i true s t=0 := by
    simp [coefficient,hr]
  apply jet_ext <;> simp only [base_form,left_form,right_form,both_form,coeff,coeffR]
  all_goals { by_cases hs : s=t <;> simp [Matrix.one_apply,hs,base,left,right,both] }
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma Q_endpoint_ne_zero : Q (-L/2)≠0 ∧ Q (-(-L/2))≠0 ∧
    Q (-L/2-Real.pi/2)≠0 ∧ Q (-(-L/2-Real.pi/2))≠0 := by
  have hp:=Real.pi_pos
  have hs : ∀ x : ℝ, 0<x → x<Real.pi → sine x≠0 := fun x h0 h1=>sine_ne_zero_interval h0 h1
  have hn : ∀ x : ℝ, -Real.pi<x → x<0 → sine x≠0 := by
    intro x h0 h1
    have h:=hs (-x) (by linarith) (by linarith)
    simpa only [sine,Real.sin_neg,Complex.ofReal_neg,neg_ne_zero] using h
  refine ⟨?_,?_,?_,?_⟩
  all_goals { unfold Q; apply mul_ne_zero <;> first | apply hs <;> simp only [L,b] <;> linarith | apply hn <;> simp only [L,b] <;> linarith }
lemma homogeneous_T_zero (n : ℕ) : T n (homogeneous n) 0=1 := by
  apply closed_at_cap n (homogeneous n) 0 cap K1_at_zero K0_at_zero
  · intro s t
    apply forward_cap_all
    intro i a c
    simpa only [exactSites,zero_add,sub_zero,homogeneous] using
      localForward_cap (-L/2) Q_endpoint_ne_zero.1 Q_endpoint_ne_zero.2.1 a c
  · exact K0_close_cap _
  · exact K1_close_cap _
lemma homogeneous_T_halfpi (n : ℕ) : T n (homogeneous n) (Real.pi/2)=1 := by
  apply closed_at_cap n (homogeneous n) (Real.pi/2) (fun p=> -(parity p.1*cap p))
    K1_at_halfpi K0_at_halfpi
  · intro s t
    apply forward_cap_all
    intro i a c
    have h:=congrArg Neg.neg (localForward_period_cap (-L/2-Real.pi/2)
      Q_endpoint_ne_zero.2.2.1 Q_endpoint_ne_zero.2.2.2 a c)
    rw [←Matrix.mulVec_neg] at h
    simpa only [exactSites,homogeneous,
      show -L/2-Real.pi/2+Real.pi=Real.pi/2+-L/2 by ring,
      show b+(-L/2-Real.pi/2)=b-Real.pi/2+-L/2 by ring,neg_ite,neg_zero,Pi.neg_def] using h
  · exact K0_close_twisted_cap _
  · exact K1_close_twisted_cap _
lemma physicalFamily_of_T_one (n : ℕ) (u : ℝ) (h : T n (homogeneous n) u=1) :
    physicalFamily n u=1 := by
  unfold physicalFamily
  rw [h,Matrix.submatrix_one_equiv,Matrix.map_one] <;> simp
lemma commonScalar_one (W : ℕ) : commonScalar W 1=1 := by
  unfold commonScalar
  rw [Matrix.one_mulVec,normalized_pair]
lemma physicalP_endpoint_zeros (W : ℕ) :
    physicalP W (3*L/2)=0 ∧ physicalP W (5*L/2)=0 := by
  have hg : gamma+3*L/2=b := by simp only [gamma,b,L];ring
  have hh : gamma+5*L/2=Real.pi/2 := by simp only [gamma,L];ring
  constructor
  · unfold physicalP
    rw [hg,show b=b-0 by ring,physicalScalar_reflection W 0
      (homogeneous_nonsingular_interval _ (by unfold gamma;linarith [Real.pi_pos])
        (by simp only [b,gamma];linarith [Real.pi_pos]))]
    unfold physicalScalar
    rw [physicalFamily_of_T_one _ _ (homogeneous_T_zero _),commonScalar_one]
    rfl
  · unfold physicalP physicalScalar
    rw [hh,physicalFamily_of_T_one _ _ (homogeneous_T_halfpi _),commonScalar_one]
    rfl
end CriticalHoneycomb.Transfer.SpectralFamily

end

end OAI
