import OAI.Analysis.CStarAlgebra.PureInfiniteness.Avoidance

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
namespace OrthogonalSlots
section GraphAlgebra
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

def graphWord (R : Fin n → A) (hR : ∀ i (k : Her h), R i * (k : A) ∈ Her h)
    (k : Her h) : A := ∑ i, S.carrier i ⟨R i * (k : A), hR i k⟩

lemma graphWord_inner (R : Fin n → A) (hR : ∀ i (k : Her h), R i * (k : A) ∈ Her h)
    (k l : Her h) :
    star (S.graphWord R hR k) * S.graphWord R hR l =
      star (k : A) * (∑ i, star (R i) * R i) * (l : A) := by
  classical
  simp only [graphWord, star_sum, Finset.sum_mul, Finset.mul_sum, S.inner]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [star_mul, mul_assoc]

lemma graphWord_outer (R : Fin n → A) (hR : ∀ i (k : Her h), R i * (k : A) ∈ Her h)
    (k l : Her h) : S.graphWord R hR k * star (S.graphWord R hR l) ∈ Her v := by
  classical
  simp only [graphWord, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact (Her v).sum_mem fun i _ => (Her v).sum_mem fun j _ => S.outer j i _ _

lemma slot_graphWord (R : Fin n → A) (hR : ∀ i (k : Her h), R i * (k : A) ∈ Her h)
    (i : Fin n) (k l : Her h) :
    star (S.carrier i k) * S.graphWord R hR l = star (k : A) * R i * (l : A) := by
  classical
  simp only [graphWord, Finset.mul_sum, S.inner]
  simp [mul_assoc]

lemma graphWord_mul (R : Fin n → A) (hR : ∀ i (k : Her h), R i * (k : A) ∈ Her h)
    (k l : Her h) : S.graphWord R hR (k*l) = S.graphWord R hR k * (l : A) := by
  classical
  simp only [graphWord, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (⟨R i * ((k*l : Her h) : A), hR i (k*l)⟩ : Her h) =
      ⟨R i * (k : A), hR i k⟩ * l := by apply Subtype.ext; exact (mul_assoc _ _ _).symm
  rw [he, S.mul]

end GraphAlgebra
end OrthogonalSlots

section UnitalGraph
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma cfc_mul_mem_Her {h q : D} (hq : q ∈ Her h) (hqa : IsSelfAdjoint q)
    (f : ℝ → ℝ) (hf : Continuous f) {k : D} (hk : k ∈ Her h) :
    cfc f q * k ∈ Her h := by
  have hm : cfcₙ (fun x => f x - f 0) q ∈ Her h := cfcₙ_mem (𝕜' := ℂ) _ hq
  have he : cfcₙ (fun x => f x - f 0) q = cfc f q - (f 0) • (1 : D) := by
    rw [cfcₙ_eq_cfc (f := fun x => f x - f 0) (a := q) ((hf.sub continuous_const).continuousOn) (by simp),
      cfc_sub f (fun _ => f 0) q hf.continuousOn continuous_const.continuousOn,
      cfc_const _ q hqa, Algebra.algebraMap_eq_smul_one]
  have he' : cfc f q = cfcₙ (fun x => f x - f 0) q + (f 0) • (1 : D) := by rw [he]; abel
  rw [he', add_mul, smul_mul_assoc, one_mul]
  exact (Her h).add_mem ((Her h).mul_mem hm hk) (real_smul_mem_Her hk _)

def graphComplement (S : Fin 4 → D) : D :=
  cfc (fun t : ℝ => Real.sqrt ((15-t)/16)) (∑ i, star (S i)*S i)

lemma graphComplement_nonneg (S : Fin 4 → D) : 0 ≤ graphComplement S :=
  cfc_nonneg fun _ _ => Real.sqrt_nonneg _

lemma graphComplement_mul_self (S : Fin 4 → D) (hS : ∀ i, ‖S i‖ ≤ 1) :
    graphComplement S * graphComplement S =
      (15/16 : ℝ) • (1 : D) - (1/16 : ℝ) • (∑ i, star (S i)*S i) := by
  rcases subsingleton_or_nontrivial D with hD | hD
  · exact Subsingleton.elim _ _
  let q := ∑ i, star (S i)*S i
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => star_mul_self_nonneg _
  have hn : ‖q‖ ≤ 4 := by
    calc
      ‖q‖ ≤ ∑ i, ‖star (S i)*S i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 4, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [CStarRing.norm_star_mul_self]
        simpa using mul_self_le_mul_self (norm_nonneg _) (hS i)
      _ = 4 := by simp
  have hc : Continuous (fun t : ℝ => Real.sqrt ((15-t)/16)) := by fun_prop
  change cfc _ q * cfc _ q = _
  rw [← cfc_mul _ _ q hc.continuousOn hc.continuousOn]
  have he : cfc (fun t : ℝ => Real.sqrt ((15-t)/16) * Real.sqrt ((15-t)/16)) q =
      cfc (fun t : ℝ => 15/16 - (1/16)*t) q := by
    apply cfc_congr
    intro t ht
    have ht' : t ≤ 4 := (Real.le_norm_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans hn)
    dsimp only
    rw [Real.mul_self_sqrt (by linarith : 0 ≤ (15-t)/16)]
    ring
  rw [he, cfc_sub (fun _ : ℝ => 15/16) (fun t : ℝ => (1/16)*t) q,
    cfc_const _ q hq.isSelfAdjoint, cfc_const_mul (1/16 : ℝ) (fun t : ℝ => t) q,
    cfc_id' ℝ q hq.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]

lemma graphComplement_mul_mem {h : D} (S : Fin 4 → D) (hS : ∀ i, S i ∈ Her h)
    {k : D} (hk : k ∈ Her h) : graphComplement S * k ∈ Her h := by
  apply cfc_mul_mem_Her ?_ ?_ _ (by fun_prop) hk
  · exact (Her h).sum_mem fun i _ => (Her h).mul_mem (StarMemClass.star_mem (s := Her h) (hS i)) (hS i)
  · exact (Finset.sum_nonneg fun i _ => star_mul_self_nonneg (S i)).isSelfAdjoint

def graphCoeffs (T : Fin 4 → D) : Fin 6 → D :=
  ![(1/4 : ℝ) • 1, (1/4 : ℝ) • T 0, (1/4 : ℝ) • T 1,
    (1/4 : ℝ) • T 2, (1/4 : ℝ) • T 3, graphComplement T]

lemma graphCoeffs_inner (T : Fin 4 → D) (hT : ∀ i, ‖T i‖ ≤ 1) :
    ∑ i, star (graphCoeffs T i) * graphCoeffs T i = 1 := by
  classical
  rw [Fin.sum_univ_six]
  dsimp [graphCoeffs]
  simp only [star_smul, star_trivial, star_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, one_mul]
  rw [(graphComplement_nonneg T).isSelfAdjoint.star_eq,
    graphComplement_mul_self T hT, Fin.sum_univ_four]
  module

lemma graphCoeffs_mem {h : D} (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h)
    (i : Fin 6) (k : Her h) : graphCoeffs T i * (k : D) ∈ Her h := by
  fin_cases i <;> dsimp [graphCoeffs] <;> try simp only [smul_mul_assoc, one_mul]
  · exact real_smul_mem_Her k.property _
  · exact real_smul_mem_Her ((Her h).mul_mem (hT 0) k.property) _
  · exact real_smul_mem_Her ((Her h).mul_mem (hT 1) k.property) _
  · exact real_smul_mem_Her ((Her h).mul_mem (hT 2) k.property) _
  · exact real_smul_mem_Her ((Her h).mul_mem (hT 3) k.property) _
  · exact graphComplement_mul_mem T hT k.property

end UnitalGraph
lemma Her_fixed_right {h t : A} (hh : IsSelfAdjoint h) (ht : h * t = h)
    {k : A} (hk : k ∈ Her h) : k * t = k := by
  have he : star t * h = h := by
    simpa only [star_mul, hh.star_eq] using congrArg star ht
  have hs := Her_fixed_left he (StarMemClass.star_mem (s := Her h) hk)
  simpa only [star_mul, star_star] using congrArg star hs

def graphInverseFn (t : ℝ) : ℝ := t / (max (1/32 : ℝ) t)^2

lemma continuous_graphInverseFn : Continuous graphInverseFn := by
  apply Continuous.div continuous_id
    (((continuous_const : Continuous (fun _ : ℝ => (1/32 : ℝ))).max continuous_id).pow 2)
  intro t
  exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/32) (le_max_left _ _)))

lemma graphInverseFn_zero : graphInverseFn 0 = 0 := by simp [graphInverseFn]

def graphInverse (X : A) : A := cfcₙ graphInverseFn X

section InverseOrder
variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma graphInverse_mem {h X : A} (hX : X ∈ Her h) : graphInverse X ∈ Her h :=
  cfcₙ_mem (𝕜' := ℂ) _ hX

lemma cut_mul_graphInverse {X : A} (hX : 0 ≤ X) :
    cut X (1/32) * (X * graphInverse X) = cut X (1/32) := by
  have hc : Continuous (fun t : ℝ => max (t-1/32) 0) := by fun_prop
  have h0 : (fun t : ℝ => max (t-1/32) 0) 0 = 0 := by norm_num
  have he : X * graphInverse X = cfcₙ (fun t : ℝ => t * graphInverseFn t) X := by
    simpa only [id_eq, cfcₙ_id' ℝ X hX.isSelfAdjoint, graphInverse] using
      (cfcₙ_mul id graphInverseFn X continuousOn_id rfl
        continuous_graphInverseFn.continuousOn graphInverseFn_zero).symm
  rw [he, cut, ← cfcₙ_mul (fun t : ℝ => max (t-1/32) 0)
    (fun t : ℝ => t * graphInverseFn t) X hc.continuousOn h0
    (continuous_id.mul continuous_graphInverseFn).continuousOn (by simp)]
  apply cfcₙ_congr
  intro t ht
  dsimp only
  by_cases h : t ≤ 1/32
  · rw [max_eq_right (sub_nonpos.mpr h), zero_mul]
  · have ht0 : t ≠ 0 := ne_of_gt (lt_trans (by norm_num) (lt_of_not_ge h))
    dsimp [graphInverseFn]
    rw [max_eq_right (le_of_not_ge h)]
    field_simp

lemma right_fixed_by_graphInverse {X S : A} (hX : 0 ≤ X)
    (hS : S ∈ Her (cut X (1/32))) : S * (X * graphInverse X) = S :=
  Her_fixed_right (cut_nonneg X (1/32)).isSelfAdjoint (cut_mul_graphInverse hX) hS

lemma map_graphInverse {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : A →⋆ₙₐ[ℂ] B) {X : A} (hX : 0 ≤ X) :
    π (graphInverse X) = graphInverse (π X) :=
  π.map_cfcₙ graphInverseFn X continuous_graphInverseFn.continuousOn graphInverseFn_zero
    (map_continuous π) hX.isSelfAdjoint (map_nonneg π hX).isSelfAdjoint

end InverseOrder
section GraphDefect
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma positive_mul_zero_of_conjugate_zero {a x : D} (ha : 0 ≤ a)
    (hz : star x * a * x = 0) : a * x = 0 := by
  have hr : CFC.sqrt a * x = 0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    calc
      star (CFC.sqrt a * x) * (CFC.sqrt a * x) =
          star x * (CFC.sqrt a * CFC.sqrt a) * x := by
        simp only [star_mul, (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, mul_assoc]
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self a ha, hz]
  rw [← CFC.sqrt_mul_sqrt_self a ha, mul_assoc, hr, mul_zero]

lemma positive_fixed_of_square_fixed {p x : D} (hp : 0 ≤ p)
    (he : p * p * x = x) : p * x = x := by
  have hi : IsUnit ((1 : D) + p) := CStarAlgebra.isUnit_of_le 1 (le_add_of_nonneg_right hp)
  apply hi.mul_left_cancel
  simp only [add_mul, one_mul, ← mul_assoc, he]
  exact add_comm _ _

lemma sqrt_fixed_of_fixed {p x : D} (hp : 0 ≤ p) (he : p*x=x) : CFC.sqrt p*x=x := by
  apply positive_fixed_of_square_fixed (CFC.sqrt_nonneg _)
  rwa [CFC.sqrt_mul_sqrt_self p hp]

lemma star_mul_le_one_of_norm_le_one {x : D} (hx : ‖x‖ ≤ 1) : star x * x ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg x)).mp
  rw [CStarRing.norm_star_mul_self]
  simpa using mul_self_le_mul_self (norm_nonneg _) hx

lemma graph_defect_forces {p c y : D} (hp : 0 ≤ p) (hpn : ‖p‖ ≤ 1)
    (hcn : ‖c‖ ≤ 1) (hy : 0 ≤ y)
    (hd : y * (1 - star c * (p*p) * c) * y = 0) :
    p * (c*y) = c*y ∧ star c * c * y = y := by
  have hp2 : 0 ≤ 1 - p*p := sub_nonneg.mpr (by
    simpa only [hp.isSelfAdjoint.star_eq] using star_mul_le_one_of_norm_le_one hpn)
  have hc2 : 0 ≤ 1 - star c*c := sub_nonneg.mpr (star_mul_le_one_of_norm_le_one hcn)
  have h₁ : 0 ≤ y*(1-star c*c)*y := by
    simpa only [hy.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg hc2 y
  have h₂ : 0 ≤ star (c*y)*(1-p*p)*(c*y) := star_left_conjugate_nonneg hp2 _
  have he : y*(1-star c*c)*y + star (c*y)*(1-p*p)*(c*y) = 0 := by
    calc
      _ = y * (1 - star c * (p*p) * c) * y := by
        simp only [star_mul, hy.isSelfAdjoint.star_eq]; noncomm_ring
      _ = 0 := hd
  have hz₁ : y*(1-star c*c)*y = 0 := le_antisymm ((le_add_of_nonneg_right h₂).trans_eq he) h₁
  have hz₂ : star (c*y)*(1-p*p)*(c*y) = 0 := le_antisymm ((le_add_of_nonneg_left h₁).trans_eq he) h₂
  have hcfix := positive_mul_zero_of_conjugate_zero hc2
    (show star y*(1-star c*c)*y=0 by simpa only [hy.isSelfAdjoint.star_eq] using hz₁)
  have hpfix := positive_mul_zero_of_conjugate_zero hp2 hz₂
  have hec : star c*c*y=y := by
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [sub_mul, one_mul] using hcfix
  have hep : p*p*(c*y)=c*y := by
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [sub_mul, one_mul] using hpfix
  exact ⟨positive_fixed_of_square_fixed hp hep, hec⟩

lemma norm_conjugate_eq_of_isometric_on {c y : D} (hy : 0 ≤ y)
    (hc : star c*c*y=y) : ‖c*y*star c‖=‖y‖ := by
  have hs := Her_fixed_left hc (sqrt_mem_Her (self_mem_Her hy) hy)
  have he : c*y*star c = (c*CFC.sqrt y)*star (c*CFC.sqrt y) := by
    simp only [star_mul, (CFC.sqrt_nonneg y).isSelfAdjoint.star_eq]
    rw [show c*y*star c = c * (CFC.sqrt y * CFC.sqrt y) * star c by rw [CFC.sqrt_mul_sqrt_self y hy]]
    simp only [mul_assoc]
  rw [he, CStarRing.norm_self_mul_star, ← CStarRing.norm_star_mul_self]
  congr 1
  calc
    star (c*CFC.sqrt y)*(c*CFC.sqrt y) = CFC.sqrt y*(star c*c*CFC.sqrt y) := by
      simp only [star_mul, (CFC.sqrt_nonneg y).isSelfAdjoint.star_eq, mul_assoc]
    _ = y := by rw [hs, CFC.sqrt_mul_sqrt_self y hy]

end GraphDefect

section GraphConstruction
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable {h a t : D} (V : OrthogonalSlots 6 h a) (ht : 0 ≤ t) (htH : t ∈ Her h)

def graphSlot (i : Fin 6) : D := V.carrier i ⟨t, htH⟩

def graphZ (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) : D :=
  V.graphWord (graphCoeffs T) (graphCoeffs_mem T hT) ⟨CFC.sqrt t, sqrt_mem_Her htH ht⟩

def graphP (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) : D :=
  graphZ V ht htH T hT * star (graphZ V ht htH T hT)

lemma graphZ_inner (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) (hn : ∀ i, ‖T i‖ ≤ 1) :
    star (graphZ V ht htH T hT) * graphZ V ht htH T hT = t := by
  rw [graphZ, V.graphWord_inner, graphCoeffs_inner T hn]
  simpa only [mul_one, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq] using CFC.sqrt_mul_sqrt_self t ht

lemma graphP_nonneg (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) : 0 ≤ graphP V ht htH T hT :=
  mul_star_self_nonneg _

lemma graphP_mem (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) : graphP V ht htH T hT ∈ Her a :=
  V.graphWord_outer _ _ _ _

lemma graphP_represented_norm {E : Type*} [NonUnitalCStarAlgebra E]
    (π : D →⋆ₙₐ[ℂ] E) (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) (hn : ∀ i, ‖T i‖ ≤ 1) :
    ‖π (graphP V ht htH T hT)‖ = ‖π t‖ := by
  rw [graphP, map_mul, map_star, CStarRing.norm_self_mul_star,
    ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul, graphZ_inner V ht htH T hT hn]

include ht in
lemma slot_sandwich_mem (i j : Fin 6) (F : D) :
    star (graphSlot V htH i) * F * graphSlot V htH j ∈ Her h := by
  let r : Her h := ⟨CFC.sqrt t, sqrt_mem_Her htH ht⟩
  have he : (⟨t, htH⟩ : Her h) = r*r := by
    apply Subtype.ext
    exact (CFC.sqrt_mul_sqrt_self t ht).symm
  have hWi : graphSlot V htH i = V.carrier i r * CFC.sqrt t := by rw [graphSlot, he, V.mul]
  have hWj : graphSlot V htH j = V.carrier j r * CFC.sqrt t := by rw [graphSlot, he, V.mul]
  rw [hWi, hWj, star_mul, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq]
  have hm := Her_sandwich (sqrt_mem_Her htH ht) (star (V.carrier i r) * F * V.carrier j r)
  simpa only [(CFC.sqrt_nonneg t).isSelfAdjoint.star_eq, mul_assoc] using hm

def graphX (F : D) : D := (16 : ℝ) • (star (graphSlot V htH 0) * F * graphSlot V htH 0)

def graphB (F : D) (i : Fin 4) : D := (16 : ℝ) •
  (star (graphSlot V htH i.castSucc.succ) * F * graphSlot V htH 0 * graphInverse (graphX V htH F))

lemma graphX_nonneg {F : D} (hF : 0 ≤ F) : 0 ≤ graphX V htH F :=
  smul_nonneg (by norm_num) (star_left_conjugate_nonneg hF _)

include ht in
lemma graphX_mem (F : D) : graphX V htH F ∈ Her h :=
  real_smul_mem_Her (slot_sandwich_mem V ht htH 0 0 F) _

include ht in
lemma graphB_mem (F : D) (i : Fin 4) : graphB V htH F i ∈ Her h :=
  real_smul_mem_Her ((Her h).mul_mem (slot_sandwich_mem V ht htH _ _ F)
    (graphInverse_mem (graphX_mem V ht htH F))) _

lemma graphSlot0_Z (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) :
    star (graphSlot V htH 0) * graphZ V ht htH T hT = (1/4 : ℝ) • (t * CFC.sqrt t) := by
  rw [graphSlot, graphZ, V.slot_graphWord]
  simp [graphCoeffs, ht.isSelfAdjoint.star_eq]

lemma graphSlot_Z (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) (i : Fin 4) :
    star (graphSlot V htH i.castSucc.succ) * graphZ V ht htH T hT =
      (1/4 : ℝ) • (t * T i * CFC.sqrt t) := by
  rw [graphSlot, graphZ, V.slot_graphWord]
  have he : graphCoeffs T i.castSucc.succ = (1/4 : ℝ) • T i := by fin_cases i <;> rfl
  rw [he, ht.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc]

lemma norm_compression_eq_of_fixed {z F : D} (hF : 0 ≤ F) (hfix : z*star z*F=F) :
    ‖star z*F*z‖=‖F‖ := by
  have hs := Her_fixed_left hfix (sqrt_mem_Her (self_mem_Her hF) hF)
  calc
    ‖star z*F*z‖ = ‖star (CFC.sqrt F*z)*(CFC.sqrt F*z)‖ := by
      congr 1
      simp only [star_mul, (CFC.sqrt_nonneg F).isSelfAdjoint.star_eq]
      calc
        star z*F*z = star z*(CFC.sqrt F*CFC.sqrt F)*z := by rw [CFC.sqrt_mul_sqrt_self F hF]
        _ = _ := by noncomm_ring
    _ = ‖(CFC.sqrt F*z)*star (CFC.sqrt F*z)‖ := by
      rw [CStarRing.norm_star_mul_self, CStarRing.norm_self_mul_star]
    _ = ‖F‖ := by
      congr 1
      calc
        (CFC.sqrt F*z)*star (CFC.sqrt F*z) = CFC.sqrt F*(z*star z*CFC.sqrt F) := by
          simp only [star_mul, (CFC.sqrt_nonneg F).isSelfAdjoint.star_eq, mul_assoc]
        _ = F := by rw [hs, CFC.sqrt_mul_sqrt_self F hF]

theorem graph_failure (htn : ‖t‖ ≤ 1) (c y : D) (hy : 0 ≤ y) (hcn : ‖c‖ ≤ 1)
    (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) (hTn : ∀ i, ‖T i‖ ≤ 1)
    (hTX : ∀ i, T i ∈ Her (cut (graphX V htH (c*y*star c)) (1/32)))
    (hd : y * (1-star c*(graphP V ht htH T hT * graphP V ht htH T hT)*c)*y=0) :
    ‖graphX V htH (c*y*star c)‖=‖y‖ ∧ ∀ i, graphB V htH (c*y*star c) i = T i := by
  let z := graphZ V ht htH T hT
  let p := z*star z
  let F := c*y*star c
  let H₀ := star z*F*z
  have hp : 0 ≤ p := mul_star_self_nonneg z
  have hpn : ‖p‖ ≤ 1 := by
    change ‖graphP V ht htH T hT‖ ≤ 1
    change ‖z*star z‖ ≤ 1
    rw [CStarRing.norm_self_mul_star, ← CStarRing.norm_star_mul_self]
    change ‖star (graphZ V ht htH T hT)*graphZ V ht htH T hT‖ ≤ 1
    rw [graphZ_inner V ht htH T hT hTn]
    exact htn
  have hz : star z*z=t := graphZ_inner V ht htH T hT hTn
  have hdf : y*(1-star c*(p*p)*c)*y=0 := hd
  obtain ⟨hpc,hcc⟩ := graph_defect_forces hp hpn hcn hy hdf
  have hF : 0 ≤ F := star_right_conjugate_nonneg hy c
  have hFH : 0 ≤ H₀ := star_left_conjugate_nonneg hF z
  have hpF : p*F=F := by
    change p*(c*y*star c)=c*y*star c
    rw [← mul_assoc, hpc]
  have hFp : F*p=F := by
    simpa only [star_mul, hF.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq] using congrArg star hpF
  have heF : F=z*H₀*star z := by
    calc
      F = p*F*p := by rw [hpF,hFp]
      _ = z*H₀*star z := by dsimp [p,H₀]; noncomm_ring
  have htH₀ : t*H₀=H₀ := by
    calc
      t*H₀ = star z*(p*F)*z := by rw [← hz]; dsimp [H₀,p]; noncomm_ring
      _ = H₀ := by rw [hpF]
  have hH₀t : H₀*t=H₀ := by
    simpa only [star_mul, hFH.isSelfAdjoint.star_eq, ht.isSelfAdjoint.star_eq] using congrArg star htH₀
  have hrH₀ : CFC.sqrt t*H₀=H₀ := sqrt_fixed_of_fixed ht htH₀
  have hH₀r : H₀*CFC.sqrt t=H₀ := by
    simpa only [star_mul, hFH.isSelfAdjoint.star_eq, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq]
      using congrArg star hrH₀
  have hW₀ : star (graphSlot V htH 0)*z=(1/4 : ℝ) • (t*CFC.sqrt t) :=
    graphSlot0_Z V ht htH T hT
  have hzW : star z*graphSlot V htH 0=(1/4 : ℝ) • (CFC.sqrt t*t) := by
    simpa only [star_mul, star_star, star_smul, star_trivial,
      ht.isSelfAdjoint.star_eq, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq] using congrArg star hW₀
  have hW (i : Fin 6) : star (graphSlot V htH i)*F*graphSlot V htH 0 =
      (star (graphSlot V htH i)*z)*H₀*(star z*graphSlot V htH 0) := by
    rw [heF]; noncomm_ring
  have hXeq : graphX V htH F=H₀ := by
    rw [graphX, hW 0, hW₀, hzW]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [show (t*CFC.sqrt t)*H₀*(CFC.sqrt t*t)=H₀ by
      rw [mul_assoc t (CFC.sqrt t) H₀, hrH₀, htH₀, ← mul_assoc, hH₀r, hH₀t]]
    norm_num
  have hX : 0 ≤ graphX V htH F := graphX_nonneg V htH hF
  refine ⟨?_, fun i => ?_⟩
  · rw [hXeq, norm_compression_eq_of_fixed hF hpF, norm_conjugate_eq_of_isometric_on hy hcc]
  · have hTi := hTX i
    change T i ∈ Her (cut (graphX V htH F) (1/32)) at hTi
    have htX : t*graphX V htH F=graphX V htH F := by rw [hXeq]; exact htH₀
    have htT : t*T i=T i := Her_fixed_left htX (Her_mono_of_mem (cut_mem_Her hX _) hTi)
    have hright := right_fixed_by_graphInverse hX hTi
    change graphB V htH F i=T i
    rw [graphB, hW i.castSucc.succ, graphSlot_Z V ht htH T hT i, hzW]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    have he : (t*T i*CFC.sqrt t)*H₀*(CFC.sqrt t*t)*graphInverse (graphX V htH F) = T i := by
      calc
        _ = (t*T i)*H₀*graphInverse (graphX V htH F) := by
          rw [mul_assoc (t*T i) (CFC.sqrt t) H₀, hrH₀,
            mul_assoc (t*T i) H₀ (CFC.sqrt t*t), ← mul_assoc H₀,
            hH₀r, hH₀t]
        _ = T i := by rw [htT, ← hXeq, mul_assoc]; exact hright
    rw [he]
    norm_num

end GraphConstruction

section AbstractMeasurements
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def measurementX (w F : D) : D := (16 : ℝ) • (star w*F*w)
def measurementB (w : Fin 6 → D) (F : D) (i : Fin 4) : D :=
  (16 : ℝ) • (star (w i.castSucc.succ)*F*w 0*graphInverse (measurementX (w 0) F))

theorem graph_failure_of_identities {t z : D} (ht : 0 ≤ t) (htn : ‖t‖ ≤ 1)
    (w : Fin 6 → D) (hz : star z*z=t) (T : Fin 4 → D)
    (hW₀ : star (w 0)*z=(1/4 : ℝ) • (t*CFC.sqrt t))
    (hWi : ∀ i : Fin 4, star (w i.castSucc.succ)*z=(1/4 : ℝ) • (t*T i*CFC.sqrt t))
    (c y : D) (hy : 0 ≤ y) (hcn : ‖c‖ ≤ 1)
    (hTX : ∀ i, T i ∈ Her (cut (measurementX (w 0) (c*y*star c)) (1/32)))
    (hd : y*(1-star c*((z*star z)*(z*star z))*c)*y=0) :
    ‖measurementX (w 0) (c*y*star c)‖=‖y‖ ∧ ∀ i, measurementB w (c*y*star c) i=T i := by
  let p := z*star z
  let F := c*y*star c
  let H₀ := star z*F*z
  have hp : 0 ≤ p := mul_star_self_nonneg z
  have hpn : ‖p‖ ≤ 1 := by
    change ‖z*star z‖ ≤ 1
    rw [CStarRing.norm_self_mul_star, ← CStarRing.norm_star_mul_self, hz]
    exact htn
  have hdf : y*(1-star c*(p*p)*c)*y=0 := hd
  obtain ⟨hpc,hcc⟩ := graph_defect_forces hp hpn hcn hy hdf
  have hF : 0 ≤ F := star_right_conjugate_nonneg hy c
  have hFH : 0 ≤ H₀ := star_left_conjugate_nonneg hF z
  have hpF : p*F=F := by
    change p*(c*y*star c)=c*y*star c
    rw [← mul_assoc, hpc]
  have hFp : F*p=F := by
    simpa only [star_mul, hF.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq] using congrArg star hpF
  have heF : F=z*H₀*star z := by
    calc
      F = p*F*p := by rw [hpF,hFp]
      _ = z*H₀*star z := by dsimp [p,H₀]; noncomm_ring
  have htH₀ : t*H₀=H₀ := by
    calc
      t*H₀ = star z*(p*F)*z := by rw [← hz]; dsimp [H₀,p]; noncomm_ring
      _ = H₀ := by rw [hpF]
  have hH₀t : H₀*t=H₀ := by
    simpa only [star_mul, hFH.isSelfAdjoint.star_eq, ht.isSelfAdjoint.star_eq] using congrArg star htH₀
  have hrH₀ : CFC.sqrt t*H₀=H₀ := sqrt_fixed_of_fixed ht htH₀
  have hH₀r : H₀*CFC.sqrt t=H₀ := by
    simpa only [star_mul, hFH.isSelfAdjoint.star_eq, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq]
      using congrArg star hrH₀
  have hzW : star z*w 0=(1/4 : ℝ) • (CFC.sqrt t*t) := by
    simpa only [star_mul, star_star, star_smul, star_trivial,
      ht.isSelfAdjoint.star_eq, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq] using congrArg star hW₀
  have hW (i : Fin 6) : star (w i)*F*w 0 =
      (star (w i)*z)*H₀*(star z*w 0) := by
    rw [heF]; noncomm_ring
  have hXeq : measurementX (w 0) F=H₀ := by
    rw [measurementX, hW 0, hW₀, hzW]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [show (t*CFC.sqrt t)*H₀*(CFC.sqrt t*t)=H₀ by
      rw [mul_assoc t (CFC.sqrt t) H₀, hrH₀, htH₀, ← mul_assoc, hH₀r, hH₀t]]
    norm_num
  have hX : 0 ≤ measurementX (w 0) F := smul_nonneg (by norm_num) (star_left_conjugate_nonneg hF (w 0))
  refine ⟨?_, fun i => ?_⟩
  · rw [hXeq, norm_compression_eq_of_fixed hF hpF, norm_conjugate_eq_of_isometric_on hy hcc]
  · have hTi := hTX i
    change T i ∈ Her (cut (measurementX (w 0) F) (1/32)) at hTi
    have htX : t*measurementX (w 0) F=measurementX (w 0) F := by rw [hXeq]; exact htH₀
    have htT : t*T i=T i := Her_fixed_left htX (Her_mono_of_mem (cut_mem_Her hX _) hTi)
    have hright := right_fixed_by_graphInverse hX hTi
    change measurementB w F i=T i
    rw [measurementB, hW i.castSucc.succ, hWi i, hzW]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    have he : (t*T i*CFC.sqrt t)*H₀*(CFC.sqrt t*t)*graphInverse (measurementX (w 0) F) = T i := by
      calc
        _ = (t*T i)*H₀*graphInverse (measurementX (w 0) F) := by
          rw [mul_assoc (t*T i) (CFC.sqrt t) H₀, hrH₀,
            mul_assoc (t*T i) H₀ (CFC.sqrt t*t), ← mul_assoc H₀,
            hH₀r, hH₀t]
        _ = T i := by rw [htT, ← hXeq, mul_assoc]; exact hright
    rw [he]
    norm_num

end AbstractMeasurements

section RepresentedGraph
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
variable (π : D →⋆ₐ[ℂ] E) {h a t : D} (V : OrthogonalSlots 6 h a)
  (ht : 0 ≤ t) (htH : t ∈ Her h)

omit [PartialOrder D] [StarOrderedRing D] [PartialOrder E] [StarOrderedRing E] in
lemma graph_map_real_smul (r : ℝ) (x : D) : π (r • x) = r • π x :=
  π.toAlgHom.map_smul_of_tower r x

lemma graph_map_inverse {X : D} (hX : 0 ≤ X) :
    π (graphInverse X)=graphInverse (π X) := map_graphInverse π.toNonUnitalStarAlgHom hX

omit [PartialOrder D] [StarOrderedRing D] [PartialOrder E] [StarOrderedRing E] in
lemma graphX_map (F : D) : π (graphX V htH F) =
    measurementX (π (graphSlot V htH 0)) (π F) := by
  simp only [graphX, measurementX, graph_map_real_smul π, map_mul, map_star]

lemma graphB_map {F : D} (hF : 0 ≤ F) (i : Fin 4) : π (graphB V htH F i) =
    measurementB (fun j => π (graphSlot V htH j)) (π F) i := by
  simp only [graphB, measurementB, graph_map_real_smul π, map_mul, map_star,
    graph_map_inverse π (graphX_nonneg V htH hF), graphX_map]

theorem graph_failure_represented (htn : ‖t‖ ≤ 1) (c y : D) (hy : 0 ≤ y) (hcn : ‖c‖ ≤ 1)
    (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) (hTn : ∀ i, ‖T i‖ ≤ 1)
    (hTX : ∀ i, T i ∈ Her (cut (graphX V htH (c*y*star c)) (1/32)))
    (hd : π (y * (1-star c*(graphP V ht htH T hT * graphP V ht htH T hT)*c)*y)=0) :
    ‖π (graphX V htH (c*y*star c))‖=‖π y‖ ∧
      ∀ i, π (graphB V htH (c*y*star c) i) = π (T i) := by
  have hF : 0 ≤ c*y*star c := star_right_conjugate_nonneg hy c
  have hm : π (CFC.sqrt t)=CFC.sqrt (π t) :=
    π.toNonUnitalStarAlgHom.map_cfcₙ NNReal.sqrt t (by fun_prop) (by simp)
      (map_continuous π) ht (map_nonneg π ht)
  have hc := graph_failure_of_identities (map_nonneg π ht)
    ((NonUnitalStarAlgHom.norm_apply_le π t).trans htn)
    (fun j => π (graphSlot V htH j)) (z := π (graphZ V ht htH T hT))
    (by simpa only [map_mul, map_star] using congrArg π (graphZ_inner V ht htH T hT hTn))
    (fun i => π (T i))
    (by simpa only [map_mul, map_star, graph_map_real_smul π, hm] using
      (congrArg π (graphSlot0_Z V ht htH T hT)))
    (fun i => by simpa only [map_mul, map_star, graph_map_real_smul π, hm] using
      (congrArg π (graphSlot_Z V ht htH T hT i)))
    (π c) (π y) (map_nonneg π hy)
    ((NonUnitalStarAlgHom.norm_apply_le π c).trans hcn) (fun i => ?_) ?_
  · simpa only [graphX_map, graphB_map π V htH hF, map_mul, map_star] using hc
  · have hmem := Her_map π.toNonUnitalStarAlgHom (hTX i)
    have hh := cut_map π.toNonUnitalStarAlgHom (graphX V htH (c*y*star c)) (1/32)
      (graphX_nonneg V htH hF).isSelfAdjoint (by norm_num)
    change π (T i) ∈ Her (π (cut (graphX V htH (c*y*star c)) (1/32))) at hmem
    change cut (π (graphX V htH (c*y*star c))) (1/32) =
      π (cut (graphX V htH (c*y*star c)) (1/32)) at hh
    rw [← hh] at hmem
    simpa only [graphX_map, map_mul, map_star] using hmem
  · simpa only [graphP, map_mul, map_star, map_sub, map_one] using hd

end RepresentedGraph

end MainGap

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
local instance graphNonvanishingOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance graphNonvanishingStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance graphOperatorOrder (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance graphOperatorStarOrder (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _

theorem graph_nonvanishing {a y c : A} (ha : 0 ≤ a) (hy : 0 ≤ y) (hcn : ‖c‖ ≤ 1)
    (hp : ∀ z : A, 0 ≤ z → z ∈ Her a → ProperlyInfinite z) :
    ∃ p : A, 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      (∀ R : HilbertRep.{u,v} A, (1/2 : ℝ) < ‖R.hom a‖ → ‖R.hom p‖=1) ∧
      (∀ R : HilbertRep.{u,v} A, R.hom (y*(1-star c*(p*p)*c)*y)=0 → ‖R.hom y‖ ≤ (1/4 : ℝ)) := by
  classical
  obtain ⟨V⟩ := (hp a ha (self_mem_Her ha)).orthogonalSlots ha 6 (by norm_num : (0:ℝ)<1/8)
  let t := ramp a (1/4) (1/2)
  have ht : 0 ≤ t := ramp_nonneg a (by norm_num)
  have htn : ‖t‖ ≤ 1 := norm_ramp_le_one a (by norm_num)
  have htH : t ∈ Her (cut a (1/8)) := by
    have hcut : cut a (1/4) ∈ Her (cut a (1/8)) := by
      have hh := cut_mem_Her (cut_nonneg a (1/8)) (1/8)
      rw [cut_cut ha (by norm_num) (by norm_num)] at hh
      convert hh using 1; norm_num
    exact Her_mono_of_mem hcut (ramp_mem_Her_cut ha (by norm_num))
  let F := c*y*star c
  have hF : 0 ≤ F := star_right_conjugate_nonneg hy c
  let X := graphX V htH F
  let B := graphB V htH F
  have hX : 0 ≤ X := graphX_nonneg V htH hF
  have hXH : X ∈ Her (cut a (1/8)) := graphX_mem V ht htH F
  have hfour : fourHer X ≤ Her (cut a (1/8)) :=
    Her_mono_of_mem (Her_mono_of_mem hXH (cut_mem_Her hX (1/32)))
  obtain ⟨T,hTn,hTX,havoid⟩ := four_avoidance_unital.{u,v} hX B (fun z hz hzm =>
    hp z hz (Her_mono_of_mem (cut_mem_Her ha (1/8)) (hfour hzm)))
  have hT : ∀ i, T i ∈ Her (cut a (1/8)) := fun i => hfour (hTX i)
  let p := graphP V ht htH T hT
  have hpn : ‖p‖ ≤ 1 := by
    have he := graphP_represented_norm V ht htH (NonUnitalStarAlgHom.id ℂ A) T hT hTn
    change ‖p‖=‖t‖ at he
    rw [he]
    exact htn
  refine ⟨p, graphP_nonneg V ht htH T hT, hpn, graphP_mem V ht htH T hT, ?_, ?_⟩
  · intro R hRa
    change ‖R.hom.toNonUnitalStarAlgHom (graphP V ht htH T hT)‖=1
    rw [graphP_represented_norm V ht htH R.hom.toNonUnitalStarAlgHom T hT hTn]
    change ‖R.hom (ramp a (1/4) (1/2))‖=1
    rw [map_ramp_sa R.hom ha.isSelfAdjoint (by norm_num)]
    exact norm_ramp_eq_one (map_nonneg R.hom ha) (by norm_num) (by norm_num) hRa.le
  · intro R hd
    by_contra! hRy
    obtain ⟨hRX,hB⟩ := graph_failure_represented R.hom V ht htH htn c y hy hcn T hT hTn hTX hd
    exact havoid R (by rw [hRX]; exact hRy)
      (fun i => (hB i).symm)
end MainGap

end

end OAI
