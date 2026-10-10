import OAI.Geometry.ConjugatePoints.Metric
import OAI.Geometry.ConjugatePoints.Cometric

namespace OAI

noncomputable section

/-!
# Tensor identities and the local and torus neck metrics.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff

namespace ThreeManifold.Tensor
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

def contract (C : n → n → n → ℝ) (u v : n → ℝ) : n → ℝ :=
  fun l => ∑ i, ∑ j, C l i j * u i * v j

lemma derivative_contract (D : n → n → n → ℝ) (z l : n) (u v w : n → ℝ) :
    (∑ k, ∑ i, ∑ j, (if i = z then (1 : ℝ) else 0) * D l j k * w k * u i * v j) =
      u z * contract D v w l := by
  calc
    (∑ k, ∑ i, ∑ j, (if i = z then (1 : ℝ) else 0) * D l j k * w k * u i * v j) =
        ∑ k, ∑ j, D l j k * w k * u z * v j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp [ite_mul]
    _ = u z * contract D v w l := by
      rw [contract, Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring

omit [DecidableEq n] in
lemma composition_contract (C : n → n → n → ℝ) (l : n) (u v w : n → ℝ) :
    (∑ k, ∑ i, ∑ j, (∑ a, C l i a * C a j k) * w k * u i * v j) =
      contract C u (contract C v w) l := by
  simp only [contract, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ k, ∑ a, C l i a * C a j k * w k * u i * v j) =
        ∑ a, ∑ j, ∑ k, C l i a * C a j k * w k * u i * v j := by
      simp only [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun k a =>
        C l i a * C a _ k * w k * u i * v _)]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma curvature_contract (C D : n → n → n → ℝ) (z l : n) (u v w : n → ℝ) :
    (∑ k, ∑ i, ∑ j,
       ((if i = z then (1 : ℝ) else 0) * D l j k -
         (if j = z then (1 : ℝ) else 0) * D l i k +
         ∑ a, (C l i a * C a j k - C l j a * C a i k)) * w k * u i * v j) =
      u z * contract D v w l - v z * contract D u w l +
        contract C u (contract C v w) l - contract C v (contract C u w) l := by
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hd' : (∑ k, ∑ i, ∑ j,
      (if j = z then (1 : ℝ) else 0) * D l i k * w k * u i * v j) =
      v z * contract D u w l := by
    convert derivative_contract D z l v u w using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hc' : (∑ k, ∑ i, ∑ j,
      (∑ a, C l j a * C a i k) * w k * u i * v j) =
      contract C v (contract C u w) l := by
    convert composition_contract C l v u w using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [derivative_contract, hd', composition_contract, hc']
  ring

end ThreeManifold.Tensor

namespace ThreeManifold.Neck
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

abbrev TVec := Fin 2 → ℝ
abbrev TMat := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vec := ℝ × TVec

def pairing (A : TMat) (u v : TVec) : ℝ := dotProduct u (A *ᵥ v)

lemma pairing_add_left (A : TMat) (u v w : TVec) :
    pairing A (u + v) w = pairing A u w + pairing A v w := by
  simp only [pairing, add_dotProduct]
lemma pairing_add_right (A : TMat) (u v w : TVec) :
    pairing A u (v + w) = pairing A u v + pairing A u w := by
  simp only [pairing, Matrix.mulVec_add, dotProduct_add]
lemma pairing_sub_left (A : TMat) (u v w : TVec) :
    pairing A (u - v) w = pairing A u w - pairing A v w := by
  simp only [pairing, sub_dotProduct]
lemma pairing_sub_right (A : TMat) (u v w : TVec) :
    pairing A u (v - w) = pairing A u v - pairing A u w := by
  simp only [pairing, Matrix.mulVec_sub, dotProduct_sub]
lemma pairing_smul_left (A : TMat) (r : ℝ) (u v : TVec) :
    pairing A (r • u) v = r * pairing A u v := by
  simp only [pairing, smul_dotProduct, smul_eq_mul]
lemma pairing_smul_right (A : TMat) (r : ℝ) (u v : TVec) :
    pairing A u (r • v) = r * pairing A u v := by
  simp only [pairing, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
lemma pairing_matrix_sub (A B : TMat) (u v : TVec) :
    pairing (A - B) u v = pairing A u v - pairing B u v := by
  simp only [pairing, Matrix.sub_mulVec, dotProduct_sub]
lemma pairing_matrix_mul (A B : TMat) (u v : TVec) :
    pairing (A * B) u v = pairing A u (B *ᵥ v) := by
  simp only [pairing, Matrix.mulVec_mulVec]
lemma pairing_symm {A : TMat} (hA : Aᵀ = A) (u v : TVec) :
    pairing A u v = pairing A v u := by
  unfold pairing
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA, dotProduct_comm]

def metric (Q : TMat) (U V : Vec) : ℝ := U.1 * V.1 + pairing Q U.2 V.2

def gamma (P A : TMat) (U V : Vec) : Vec :=
  (-(1 / 2 : ℝ) * pairing A U.2 V.2,
    (1 / 2 : ℝ) • (U.1 • (P *ᵥ (A *ᵥ V.2)) + V.1 • (P *ᵥ (A *ᵥ U.2))))

def gammaPrime (P A B : TMat) (U V : Vec) : Vec :=
  (-(1 / 2 : ℝ) * pairing B U.2 V.2,
    (1 / 2 : ℝ) •
      (U.1 • ((P * B - P * A * P * A) *ᵥ V.2) +
       V.1 • ((P * B - P * A * P * A) *ᵥ U.2)))

def curvatureJet (P A B : TMat) (U V W : Vec) : Vec :=
  U.1 • gammaPrime P A B V W - V.1 • gammaPrime P A B U W +
    gamma P A U (gamma P A V W) - gamma P A V (gamma P A U W)

lemma metric_add_right (Q : TMat) (U V W : Vec) :
    metric Q U (V + W) = metric Q U V + metric Q U W := by
  simp only [metric, Prod.fst_add, Prod.snd_add, pairing_add_right]
  ring
lemma metric_sub_right (Q : TMat) (U V W : Vec) :
    metric Q U (V - W) = metric Q U V - metric Q U W := by
  simp only [metric, Prod.fst_sub, Prod.snd_sub, pairing_sub_right]
  ring
lemma metric_smul_right (Q : TMat) (r : ℝ) (U V : Vec) :
    metric Q U (r • V) = r * metric Q U V := by
  simp only [metric, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, pairing_smul_right]
  ring
lemma metric_symm {Q : TMat} (hQ : Qᵀ = Q) (U V : Vec) :
    metric Q U V = metric Q V U := by
  rw [metric, metric, pairing_symm hQ]
  ring

lemma pairing_inverse {P Q : TMat} (hQP : Q * P = 1) (u v : TVec) :
    pairing Q u (P *ᵥ v) = dotProduct u v := by
  simp only [pairing, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]

lemma metric_gamma {P Q : TMat} (hQP : Q * P = 1) (A : TMat) (U V W : Vec) :
    metric Q U (gamma P A V W) =
      -(1 / 2 : ℝ) * U.1 * pairing A V.2 W.2 +
       (1 / 2 : ℝ) * V.1 * pairing A U.2 W.2 +
       (1 / 2 : ℝ) * W.1 * pairing A U.2 V.2 := by
  simp only [metric, gamma, pairing_smul_right, pairing_add_right,
    pairing_inverse hQP]
  simp only [pairing]
  ring

lemma metric_gammaPrime {P Q : TMat} (hQP : Q * P = 1) (A B : TMat) (U V W : Vec) :
    metric Q U (gammaPrime P A B V W) =
      -(1 / 2 : ℝ) * U.1 * pairing B V.2 W.2 +
       (1 / 2 : ℝ) * V.1 * pairing (B - A * P * A) U.2 W.2 +
       (1 / 2 : ℝ) * W.1 * pairing (B - A * P * A) U.2 V.2 := by
  have h (v : TVec) : Q *ᵥ ((P * B - P * A * P * A) *ᵥ v) =
      (B - A * P * A) *ᵥ v := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_sub, ← Matrix.mul_assoc, hQP,
      Matrix.one_mul]
  simp only [metric, gammaPrime, pairing_smul_right, pairing_add_right]
  simp only [pairing, h]
  ring

lemma metric_add_left (Q : TMat) (U V W : Vec) :
    metric Q (U + V) W = metric Q U W + metric Q V W := by
  simp only [metric, Prod.fst_add, Prod.snd_add, pairing_add_left]
  ring

lemma sandwich_transpose {P A : TMat} (hP : Pᵀ = P) (hA : Aᵀ = A) :
    (A * P * A)ᵀ = A * P * A := by
  simp only [Matrix.transpose_mul, hA, hP, Matrix.mul_assoc]

lemma pairing_sandwich (P A : TMat) (u v : TVec) :
    pairing A u (P *ᵥ (A *ᵥ v)) = pairing (A * P * A) u v := by
  simp only [pairing, Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma pairing_sandwich_left {P A : TMat} (hP : Pᵀ = P) (hA : Aᵀ = A) (u v : TVec) :
    pairing A (P *ᵥ (A *ᵥ u)) v = pairing (A * P * A) u v := by
  rw [pairing_symm hA, pairing_sandwich, pairing_symm (sandwich_transpose hP hA)]

lemma curvature_contraction {P Q A B : TMat} (hQP : Q * P = 1)
    (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B) (V T : Vec) :
    metric Q V (curvatureJet P A B V T T) =
      -(1 / 2 : ℝ) * pairing B (V.1 • T.2 - T.1 • V.2) (V.1 • T.2 - T.1 • V.2) +
       (1 / 4 : ℝ) * pairing (A * P * A)
         (V.1 • T.2 - T.1 • V.2) (V.1 • T.2 - T.1 • V.2) +
       (1 / 4 : ℝ) * ((pairing A V.2 T.2) ^ 2 -
         pairing A V.2 V.2 * pairing A T.2 T.2) := by
  have hS := sandwich_transpose hP hA
  simp only [curvatureJet, metric_sub_right, metric_add_right, metric_smul_right,
    metric_gammaPrime hQP, metric_gamma hQP]
  dsimp only [gamma]
  simp only [pairing_sub_left, pairing_sub_right, pairing_smul_left, pairing_smul_right,
    pairing_add_right, pairing_sandwich, pairing_matrix_sub,
    pairing_symm hB T.2 V.2,
    pairing_symm hS T.2 V.2]
  ring

def coordinateEnergyDensity (Q A B : TMat) (T V Vdot : Vec) : ℝ :=
  Vdot.1 ^ 2 + pairing Q Vdot.2 Vdot.2 +
    2 * V.1 * pairing A Vdot.2 T.2 + (1 / 2 : ℝ) * V.1 ^ 2 * pairing B T.2 T.2

def boundaryTerm (A : TMat) (T V : Vec) : ℝ :=
  -(1 / 2 : ℝ) * T.1 * pairing A V.2 V.2 + V.1 * pairing A T.2 V.2

lemma boundaryTerm_eq {P Q : TMat} (hQP : Q * P = 1) (A : TMat) (T V : Vec) :
    boundaryTerm A T V = metric Q T (gamma P A V V) := by
  rw [metric_gamma hQP]
  unfold boundaryTerm
  ring

def boundaryJet (P A B : TMat) (T V Vdot : Vec) : ℝ :=
  -(1 / 4 : ℝ) * pairing A T.2 T.2 * pairing A V.2 V.2 -
    T.1 * pairing A Vdot.2 V.2 - (1 / 2 : ℝ) * T.1 ^ 2 * pairing B V.2 V.2 +
    Vdot.1 * pairing A V.2 T.2 + V.1 * pairing A Vdot.2 T.2 +
    V.1 * T.1 * pairing B V.2 T.2 - V.1 * T.1 * pairing (A * P * A) V.2 T.2

lemma index_density_identity {P Q A B : TMat} (hQP : Q * P = 1)
    (hQ : Qᵀ = Q) (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B) (T V Vdot : Vec) :
    metric Q (Vdot + gamma P A T V) (Vdot + gamma P A T V) -
      metric Q V (curvatureJet P A B V T T) =
        coordinateEnergyDensity Q A B T V Vdot - boundaryJet P A B T V Vdot := by
  have hS := sandwich_transpose hP hA
  rw [metric_add_left, metric_add_right, metric_add_right,
    metric_symm hQ (gamma P A T V) Vdot,
    curvature_contraction hQP hP hA hB]
  simp only [metric_gamma hQP]
  dsimp only [gamma]
  simp only [coordinateEnergyDensity, boundaryJet, pairing_sub_left, pairing_sub_right,
    pairing_smul_left, pairing_smul_right, pairing_add_left, pairing_sandwich_left hP hA,
    pairing_symm hA T.2 V.2, pairing_symm hB T.2 V.2,
    pairing_symm hS T.2 V.2]
  simp only [metric]
  ring

lemma pairing_hasDerivAt {A : ℝ → TMat} {u v : ℝ → TVec}
    {A' : TMat} {u' v' : TVec} {s : ℝ}
    (hA : HasDerivAt A A' s) (hu : HasDerivAt u u' s) (hv : HasDerivAt v v' s) :
    HasDerivAt (fun r => pairing (A r) (u r) (v r))
      (pairing (A s) u' (v s) + pairing A' (u s) (v s) +
        pairing (A s) (u s) v') s := by
  have hAe (i j : Fin 2) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j
  have hue (i : Fin 2) := hasDerivAt_pi.mp hu i
  have hve (i : Fin 2) := hasDerivAt_pi.mp hv i
  have h := ((hue 0).mul (((hAe 0 0).mul (hve 0)).add ((hAe 0 1).mul (hve 1)))).add
    ((hue 1).mul (((hAe 1 0).mul (hve 0)).add ((hAe 1 1).mul (hve 1))))
  convert! h using 1
  · funext r
    simp only [pairing, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Pi.add_apply, Pi.mul_apply]
  · simp only [pairing, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Pi.add_apply, Pi.mul_apply]
    ring

lemma pairing_matrix_smul (A : TMat) (r : ℝ) (u v : TVec) :
    pairing (r • A) u v = r * pairing A u v := by
  simp only [pairing, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma boundaryTerm_hasDerivAt {A : ℝ → TMat} {t v w : ℝ → ℝ} {u z : ℝ → TVec}
    {P B : TMat} {w' : ℝ} {z' : TVec} {s : ℝ}
    (hP : Pᵀ = P) (hAs : (A (t s))ᵀ = A (t s)) (hB : Bᵀ = B)
    (hA : HasDerivAt A B (t s)) (ht : HasDerivAt t (v s) s)
    (hv : HasDerivAt v ((1 / 2 : ℝ) * pairing (A (t s)) (u s) (u s)) s)
    (hu : HasDerivAt u (-v s • (P *ᵥ (A (t s) *ᵥ u s))) s)
    (hw : HasDerivAt w w' s) (hz : HasDerivAt z z' s) :
    HasDerivAt (fun r => boundaryTerm (A (t r)) (v r, u r) (w r, z r))
      (boundaryJet P (A (t s)) B (v s, u s) (w s, z s) (w', z')) s := by
  have hAc := hA.scomp s ht
  have hzz := pairing_hasDerivAt hAc hz hz
  have huz := pairing_hasDerivAt hAc hu hz
  have h := ((hv.const_mul (-(1 / 2 : ℝ))).mul hzz).add (hw.mul huz)
  convert! h using 1
  simp only [boundaryJet, Function.comp_apply, pairing_matrix_smul,
      pairing_smul_left, pairing_sandwich_left hP hAs,
      pairing_symm hAs (z s) z', pairing_symm hAs (u s) (z s),
      pairing_symm hAs (u s) z', pairing_symm hB (u s) (z s),
      pairing_symm (sandwich_transpose hP hAs) (u s) (z s)]
  ring

lemma continuous_pairing : Continuous (fun p : TMat × TVec × TVec =>
    pairing p.1 p.2.1 p.2.2) := by
  unfold pairing Matrix.mulVec dotProduct
  fun_prop

lemma Continuous.pairing {X : Type*} [TopologicalSpace X]
    {A : X → TMat} {u v : X → TVec} (hA : Continuous A)
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun s => pairing (A s) (u s) (v s)) :=
  continuous_pairing.comp (hA.prodMk (hu.prodMk hv))

lemma continuousOn_pairing {X : Type*} [TopologicalSpace X]
    {A : X → TMat} {u v : X → TVec} {S : Set X}
    (hA : ContinuousOn A S) (hu : ContinuousOn u S) (hv : ContinuousOn v S) :
    ContinuousOn (fun s => pairing (A s) (u s) (v s)) S :=
  continuous_pairing.comp_continuousOn (hA.prodMk (hu.prodMk hv))

lemma continuousOn_energy {X : Type*} [TopologicalSpace X] {S : Set X}
    {Q A B : X → TMat} {T V Vdot : X → Vec}
    (hQ : ContinuousOn Q S) (hA : ContinuousOn A S) (hB : ContinuousOn B S)
    (hT : ContinuousOn T S) (hV : ContinuousOn V S) (hVdot : ContinuousOn Vdot S) :
    ContinuousOn (fun s => coordinateEnergyDensity (Q s) (A s) (B s)
      (T s) (V s) (Vdot s)) S := by
  unfold coordinateEnergyDensity
  exact ((hVdot.fst.pow 2).add (continuousOn_pairing hQ hVdot.snd hVdot.snd)).add
    (((continuousOn_const.mul hV.fst).mul (continuousOn_pairing hA hVdot.snd hT.snd))) |>.add
    ((continuousOn_const.mul (hV.fst.pow 2)).mul (continuousOn_pairing hB hT.snd hT.snd))

lemma continuousOn_boundaryJet {X : Type*} [TopologicalSpace X] {S : Set X}
    {P A B : X → TMat} {T V Vdot : X → Vec}
    (hP : ContinuousOn P S) (hA : ContinuousOn A S) (hB : ContinuousOn B S)
    (hT : ContinuousOn T S) (hV : ContinuousOn V S) (hVdot : ContinuousOn Vdot S) :
    ContinuousOn (fun s => boundaryJet (P s) (A s) (B s)
      (T s) (V s) (Vdot s)) S := by
  unfold boundaryJet
  have hS : ContinuousOn (fun s => A s * P s * A s) S := (hA.mul hP).mul hA
  exact ((((((continuousOn_const.mul (continuousOn_pairing hA hT.snd hT.snd)).mul
    (continuousOn_pairing hA hV.snd hV.snd)).sub
    (hT.fst.mul (continuousOn_pairing hA hVdot.snd hV.snd))).sub
    ((continuousOn_const.mul (hT.fst.pow 2)).mul (continuousOn_pairing hB hV.snd hV.snd))).add
    (hVdot.fst.mul (continuousOn_pairing hA hV.snd hT.snd))).add
    (hV.fst.mul (continuousOn_pairing hA hVdot.snd hT.snd))).add
    ((hV.fst.mul hT.fst).mul (continuousOn_pairing hB hV.snd hT.snd)) |>.sub
    ((hV.fst.mul hT.fst).mul (continuousOn_pairing hS hV.snd hT.snd))

lemma coordinate_index_integral
    {P Q A B : ℝ → TMat} {t v w : ℝ → ℝ} {u z : ℝ → TVec}
    {wd : ℝ → ℝ} {zd : ℝ → TVec} {a c : ℝ}
    (hP : ContinuousOn (P ∘ t) (Set.uIcc a c))
    (hQ : ContinuousOn (Q ∘ t) (Set.uIcc a c))
    (hA : ContinuousOn (A ∘ t) (Set.uIcc a c))
    (hB : ContinuousOn (B ∘ t) (Set.uIcc a c))
    (hv : ContinuousOn v (Set.uIcc a c)) (hu : ContinuousOn u (Set.uIcc a c))
    (hw : ContinuousOn w (Set.uIcc a c)) (hz : ContinuousOn z (Set.uIcc a c))
    (hwd : ContinuousOn wd (Set.uIcc a c)) (hzd : ContinuousOn zd (Set.uIcc a c))
    (hQP : ∀ s ∈ Set.uIcc a c, Q (t s) * P (t s) = 1)
    (hQs : ∀ s ∈ Set.uIcc a c, (Q (t s))ᵀ = Q (t s))
    (hPs : ∀ s ∈ Set.uIcc a c, (P (t s))ᵀ = P (t s))
    (hAs : ∀ s ∈ Set.uIcc a c, (A (t s))ᵀ = A (t s))
    (hBs : ∀ s ∈ Set.uIcc a c, (B (t s))ᵀ = B (t s))
    (ht : ∀ s ∈ Set.uIcc a c, HasDerivAt t (v s) s)
    (hv' : ∀ s ∈ Set.uIcc a c,
      HasDerivAt v ((1 / 2 : ℝ) * pairing (A (t s)) (u s) (u s)) s)
    (hu' : ∀ s ∈ Set.uIcc a c,
      HasDerivAt u (-v s • (P (t s) *ᵥ (A (t s) *ᵥ u s))) s)
    (hA' : ∀ s ∈ Set.uIcc a c, HasDerivAt A (B (t s)) (t s))
    (hw' : ∀ s ∈ Set.uIcc a c, HasDerivAt w (wd s) s)
    (hz' : ∀ s ∈ Set.uIcc a c, HasDerivAt z (zd s) s) :
    (∫ s in a..c,
      metric (Q (t s)) ((wd s, zd s) + gamma (P (t s)) (A (t s)) (v s, u s) (w s, z s))
        ((wd s, zd s) + gamma (P (t s)) (A (t s)) (v s, u s) (w s, z s)) -
      metric (Q (t s)) (w s, z s)
        (curvatureJet (P (t s)) (A (t s)) (B (t s)) (w s, z s) (v s, u s) (v s, u s))) =
    (∫ s in a..c,
      coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
        (v s, u s) (w s, z s) (wd s, zd s)) -
      (boundaryTerm (A (t c)) (v c, u c) (w c, z c) -
        boundaryTerm (A (t a)) (v a, u a) (w a, z a)) := by
  let e (s : ℝ) := coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
    (v s, u s) (w s, z s) (wd s, zd s)
  let b (s : ℝ) := boundaryJet (P (t s)) (A (t s)) (B (t s))
    (v s, u s) (w s, z s) (wd s, zd s)
  have he : ContinuousOn e (Set.uIcc a c) :=
    continuousOn_energy hQ hA hB (hv.prodMk hu) (hw.prodMk hz) (hwd.prodMk hzd)
  have hb : ContinuousOn b (Set.uIcc a c) :=
    continuousOn_boundaryJet hP hA hB (hv.prodMk hu) (hw.prodMk hz) (hwd.prodMk hzd)
  have hderiv : ∀ s ∈ Set.uIcc a c,
      HasDerivAt (fun r => boundaryTerm (A (t r)) (v r, u r) (w r, z r)) (b s) s := by
    intro s hs
    exact boundaryTerm_hasDerivAt (hPs s hs) (hAs s hs) (hBs s hs)
      (hA' s hs) (ht s hs) (hv' s hs) (hu' s hs) (hw' s hs) (hz' s hs)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hb.intervalIntegrable
  calc
    _ = ∫ s in a..c, e s - b s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact index_density_identity (hQP s hs) (hQs s hs) (hPs s hs) (hAs s hs)
        (hBs s hs) _ _ _
    _ = (∫ s in a..c, e s) - ∫ s in a..c, b s :=
      intervalIntegral.integral_sub he.intervalIntegrable hb.intervalIntegrable
    _ = _ := by rw [hFTC]

lemma pairing_matrix_add (A B : TMat) (u v : TVec) :
    pairing (A + B) u v = pairing A u v + pairing B u v := by
  simp only [pairing, Matrix.add_mulVec, dotProduct_add]

lemma pairing_matrix_neg (A : TMat) (u v : TVec) :
    pairing (-A) u v = -pairing A u v := by
  simp only [pairing, Matrix.neg_mulVec, dotProduct_neg]

lemma pairing_mulVec_left (A L : TMat) (u v : TVec) :
    pairing A (L *ᵥ u) v = pairing (Lᵀ * A) u v := by
  unfold pairing
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

lemma pairing_mulVec_right (A L : TMat) (u v : TVec) :
    pairing A u (L *ᵥ v) = pairing (A * L) u v := by
  simp only [pairing, Matrix.mulVec_mulVec]

lemma energy_cometric_identity {P Q H K : TMat} (hQP : Q * P = 1)
    (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hH : Hᵀ = H)
    (p : TVec) (v : ℝ) (V Vdot : Vec) :
    coordinateEnergyDensity Q (-Q * H * Q)
      ((2 : ℝ) • (Q * H * Q * H * Q) - Q * K * Q) (v, P *ᵥ p) V Vdot =
    Vdot.1 ^ 2 + pairing Q (Vdot.2 - V.1 • (H *ᵥ p))
      (Vdot.2 - V.1 • (H *ᵥ p)) - (1 / 2 : ℝ) * pairing K p p * V.1 ^ 2 := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hfirst : (-Q * H * Q) * P = -(Q * H) := by
    rw [Matrix.mul_assoc, hQP, Matrix.mul_one, neg_mul]
  have hsecond : P * ((2 : ℝ) • (Q * H * Q * H * Q) - Q * K * Q) * P =
      (2 : ℝ) • (H * Q * H) - K := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hQP, Matrix.mul_one]
  have hHQH : pairing (H * Q * H) p p = pairing Q (H *ᵥ p) (H *ᵥ p) := by
    rw [pairing_mulVec_left, pairing_mulVec_right, hH]
  simp only [coordinateEnergyDensity, pairing_mulVec_right, pairing_mulVec_left,
    hP, hfirst]
  rw [← Matrix.mul_assoc, hsecond, pairing_matrix_sub, pairing_matrix_smul, hHQH]
  simp only [pairing_sub_left, pairing_sub_right, pairing_smul_left, pairing_smul_right,
    pairing_matrix_neg]
  rw [← pairing_mulVec_right Q H, pairing_symm hQ (H *ᵥ p) Vdot.2]
  ring

lemma matrix_mul_hasDerivAt {M N : ℝ → TMat} {M' N' : TMat} {s : ℝ}
    (hM : HasDerivAt M M' s) (hN : HasDerivAt N N' s) :
    HasDerivAt (fun r => M r * N r) (M' * N s + M s * N') s := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h (k : Fin 2) (_hk : k ∈ Finset.univ) :=
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hN k) j)
  convert! HasDerivAt.fun_sum h using 1
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

lemma mulVec_hasDerivAt {M : ℝ → TMat} {u : ℝ → TVec} {M' : TMat} {u' : TVec} {s : ℝ}
    (hM : HasDerivAt M M' s) (hu : HasDerivAt u u' s) :
    HasDerivAt (fun r => M r *ᵥ u r) (M' *ᵥ u s + M s *ᵥ u') s := by
  apply hasDerivAt_pi.mpr
  intro i
  have h (k : Fin 2) (_hk : k ∈ Finset.univ) :=
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) k).mul (hasDerivAt_pi.mp hu k)
  convert! HasDerivAt.fun_sum h using 1
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Finset.sum_add_distrib]

lemma inverse_first_jet {P Q : ℝ → TMat} {H A : TMat} {s : ℝ}
    (hP : HasDerivAt P H s) (hQ : HasDerivAt Q A s)
    (hPQ : ∀ᶠ r in nhds s, P r * Q r = 1) (hQP : Q s * P s = 1) :
    A = -Q s * H * Q s := by
  have hprod := matrix_mul_hasDerivAt hP hQ
  have heq : (fun _ : ℝ => (1 : TMat)) =ᶠ[nhds s] (fun r => P r * Q r) :=
    Filter.Eventually.mono hPQ (fun _ h => h.symm)
  have hzero : H * Q s + P s * A = 0 :=
    (hprod.congr_of_eventuallyEq heq).unique (hasDerivAt_const s (1 : TMat))
  have h := congrArg (fun N : TMat => Q s * N) hzero
  simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, hQP, Matrix.one_mul] at h
  calc
    A = -(Q s * H * Q s) := (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using h)
    _ = _ := by simp only [neg_mul]

lemma momentum_hasDerivAt_zero {Q : ℝ → TMat} {t v : ℝ → ℝ} {u : ℝ → TVec}
    {P A : TMat} {s : ℝ} (hQP : Q (t s) * P = 1)
    (hQ : HasDerivAt Q A (t s)) (ht : HasDerivAt t (v s) s)
    (hu : HasDerivAt u (-v s • (P *ᵥ (A *ᵥ u s))) s) :
    HasDerivAt (fun r => Q (t r) *ᵥ u r) 0 s := by
  have h := mulVec_hasDerivAt (hQ.scomp s ht) hu
  convert! h using 1
  simp only [Function.comp_apply, Matrix.smul_mulVec, neg_smul, Matrix.mulVec_neg,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQP, Matrix.one_mul,
    add_neg_cancel]

def splitVector (x : E3) : Vec := (x 0, ![x 1, x 2])
def joinVector (u : Vec) : E3 := ![u.1, u.2 0, u.2 1]
def blockMatrix (Q : TMat) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Q 0 0, Q 0 1; 0, Q 1 0, Q 1 1]
def blockJet (A : TMat) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

lemma join_split (x : E3) : joinVector (splitVector x) = x := by
  ext i
  fin_cases i <;> rfl
lemma split_join (u : Vec) : splitVector (joinVector u) = u := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

lemma blockMatrix_mul (P Q : TMat) :
    blockMatrix P * blockMatrix Q = blockMatrix (P * Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
lemma blockMatrix_one : blockMatrix (1 : TMat) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
lemma blockMatrix_inverse {P Q : TMat} (hQP : Q * P = 1) :
    (blockMatrix Q)⁻¹ = blockMatrix P := by
  apply Matrix.inv_eq_right_inv
  rw [blockMatrix_mul, hQP, blockMatrix_one]

lemma block_entry_hasDerivAt {Q : ℝ → TMat} {A : TMat} {s : ℝ}
    (hQ : HasDerivAt Q A s) (i j : Fin 3) :
    HasDerivAt (fun r => blockMatrix (Q r) i j) (blockJet A i j) s := by
  have h (k l : Fin 2) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hQ k) l
  fin_cases i <;> fin_cases j <;>
    simp only [blockMatrix, blockJet] <;>
    first | exact hasDerivAt_const _ _ | exact h _ _

lemma coordPartial_block {Q : ℝ → TMat} {A : TMat} {x : E3}
    (hQ : HasDerivAt Q A (x 0)) (i j k : Fin 3) :
    coordPartial (fun y => blockMatrix (Q (y 0)) i j) x k =
      (if k = 0 then 1 else 0) * blockJet A i j := by
  have h := (block_entry_hasDerivAt hQ i j).hasFDerivAt.comp x
    (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  change HasFDerivAt (fun y : E3 => blockMatrix (Q (y 0)) i j) _ x at h
  change (fderiv ℝ (fun y : E3 => blockMatrix (Q (y 0)) i j) x) (basisVector k) = _
  rw [h.fderiv]
  fin_cases k <;> simp [basisVector, ContinuousLinearMap.comp_apply]

lemma coordPartial_congr_germ {f h : E3 → ℝ} {x : E3}
    (heq : f =ᶠ[nhds x] h) (i : Fin 3) :
    coordPartial f x i = coordPartial h x i := by
  rw [coordPartial, coordPartial, heq.fderiv_eq]

lemma christoffel_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q : ℝ → TMat} {P A : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hQ : HasDerivAt Q A (x 0)) (hQP : Q (x 0) * P = 1)
    (i j k : Fin 3) :
    christoffel g c x i j k = (1 / 2 : ℝ) * ∑ l : Fin 3,
      blockMatrix P i l *
        ((if j = 0 then 1 else 0) * blockJet A l k +
         (if k = 0 then 1 else 0) * blockJet A l j -
         (if l = 0 then 1 else 0) * blockJet A j k) := by
  have hentry (a b d : Fin 3) :
      coordPartial (fun y => metricMatrix g c y a b) x d =
        (if d = 0 then 1 else 0) * blockJet A a b := by
    rw [coordPartial_congr_germ
      (Filter.Eventually.mono hg (fun _ h => congrFun (congrFun h a) b))]
    exact coordPartial_block hQ a b d
  rw [christoffel, hg.eq_of_nhds, blockMatrix_inverse hQP]
  simp only [hentry]

lemma connectionTerm_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q : ℝ → TMat} {P A : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hQ : HasDerivAt Q A (x 0)) (hQP : Q (x 0) * P = 1)
    (hA : Aᵀ = A) (u v : E3) :
    connectionTerm g c x u v =
      joinVector (gamma P A (splitVector u) (splitVector v)) := by
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
  ext i
  fin_cases i <;>
    simp [connectionTerm, christoffel_product g c hg hQ hQP,
      blockMatrix, blockJet, joinVector, gamma, splitVector, pairing,
      dotProduct, Matrix.mulVec, Fin.sum_univ_succ, h10] <;> ring

lemma join_gamma_hasDerivAt {P A : ℝ → TMat} {B : TMat} {s : ℝ}
    (hP : HasDerivAt P (-P s * A s * P s) s) (hA : HasDerivAt A B s)
    (U V : Vec) :
    HasDerivAt (fun r => joinVector (gamma (P r) (A r) U V))
      (joinVector (gammaPrime (P s) (A s) B U V)) s := by
  have hPA : HasDerivAt (fun r => P r * A r)
      (P s * B - P s * A s * P s * A s) s := by
    convert! matrix_mul_hasDerivAt hP hA using 1
    simp only [neg_mul, sub_eq_add_neg, add_comm]
  have hU := mulVec_hasDerivAt hPA (hasDerivAt_const s U.2)
  have hV := mulVec_hasDerivAt hPA (hasDerivAt_const s V.2)
  simp only [Matrix.mulVec_zero, add_zero] at hU hV
  have htor := ((hV.const_smul U.1).add (hU.const_smul V.1)).const_smul (1 / 2 : ℝ)
  have hpair := pairing_hasDerivAt hA (hasDerivAt_const s U.2)
    (hasDerivAt_const s V.2)
  simp only [pairing, dotProduct_zero, zero_dotProduct, Matrix.mulVec_zero,
    zero_add, add_zero] at hpair
  have hbase := hpair.const_mul (-(1 / 2 : ℝ))
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hbase using 1
  · convert! hasDerivAt_pi.mp htor 0 using 1
    funext r
    change ((1 / 2 : ℝ) • (U.1 • (P r *ᵥ (A r *ᵥ V.2)) +
      V.1 • (P r *ᵥ (A r *ᵥ U.2)))) 0 = _
    simp only [Matrix.mulVec_mulVec, Pi.smul_apply, Pi.add_apply]
  · convert! hasDerivAt_pi.mp htor 1 using 1
    funext r
    change ((1 / 2 : ℝ) • (U.1 • (P r *ᵥ (A r *ᵥ V.2)) +
      V.1 • (P r *ᵥ (A r *ᵥ U.2)))) 1 = _
    simp only [Matrix.mulVec_mulVec, Pi.smul_apply, Pi.add_apply]

lemma connectionTerm_basis {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x : E3) (i j k : Fin 3) :
    connectionTerm g c x (basisVector j) (basisVector k) i = christoffel g c x i j k := by
  simp [connectionTerm, basisVector, Pi.single_apply]

lemma coordPartial_join_gamma {P A : ℝ → TMat} {B : TMat} {x : E3}
    (hP : HasDerivAt P (-P (x 0) * A (x 0) * P (x 0)) (x 0))
    (hA : HasDerivAt A B (x 0)) (U V : Vec) (i k : Fin 3) :
    coordPartial (fun y => joinVector (gamma (P (y 0)) (A (y 0)) U V) i) x k =
      (if k = 0 then 1 else 0) *
        joinVector (gammaPrime (P (x 0)) (A (x 0)) B U V) i := by
  have h := (hasDerivAt_pi.mp (join_gamma_hasDerivAt hP hA U V) i).hasFDerivAt.comp x
    (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  change HasFDerivAt
    (fun y : E3 => joinVector (gamma (P (y 0)) (A (y 0)) U V) i) _ x at h
  change (fderiv ℝ
    (fun y : E3 => joinVector (gamma (P (y 0)) (A (y 0)) U V) i) x) (basisVector k) = _
  rw [h.fderiv]
  fin_cases k <;> simp [basisVector, ContinuousLinearMap.comp_apply]

lemma christoffel_product_germ {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q P A : ℝ → TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hj : ∀ᶠ r in nhds (x 0), HasDerivAt Q (A r) r ∧ Q r * P r = 1 ∧ (A r)ᵀ = A r)
    (i j k : Fin 3) :
    (fun y => christoffel g c y i j k) =ᶠ[nhds x]
      (fun y => joinVector (gamma (P (y 0)) (A (y 0))
        (splitVector (basisVector j)) (splitVector (basisVector k))) i) := by
  have hjx := (continuous_apply (0 : Fin 3)).continuousAt.tendsto.eventually hj
  filter_upwards [hg.eventuallyEq_nhds, hjx] with y hgy hy
  have h := congrFun (connectionTerm_product g c hgy hy.1 hy.2.1 hy.2.2
    (basisVector j) (basisVector k)) i
  rwa [connectionTerm_basis] at h

lemma christoffel_partial_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q P A : ℝ → TMat} {B : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hj : ∀ᶠ r in nhds (x 0), HasDerivAt Q (A r) r ∧ Q r * P r = 1 ∧ (A r)ᵀ = A r)
    (hP : HasDerivAt P (-P (x 0) * A (x 0) * P (x 0)) (x 0))
    (hA : HasDerivAt A B (x 0)) (i j k d : Fin 3) :
    coordPartial (fun y => christoffel g c y i j k) x d =
      (if d = 0 then 1 else 0) * joinVector (gammaPrime (P (x 0)) (A (x 0)) B
        (splitVector (basisVector j)) (splitVector (basisVector k))) i := by
  rw [coordPartial_congr_germ (christoffel_product_germ g c hg hj i j k)]
  exact coordPartial_join_gamma hP hA _ _ i d

lemma join_add (U V : Vec) : joinVector (U + V) = joinVector U + joinVector V := by
  ext i
  fin_cases i <;> rfl
lemma join_sub (U V : Vec) : joinVector (U - V) = joinVector U - joinVector V := by
  ext i
  fin_cases i <;> rfl
lemma join_smul (r : ℝ) (U : Vec) : joinVector (r • U) = r • joinVector U := by
  ext i
  fin_cases i <;> rfl

lemma gammaPrime_contract (P A B : TMat) (u v : E3) :
    Tensor.contract (fun l i j => joinVector (gammaPrime P A B
      (splitVector (basisVector i)) (splitVector (basisVector j))) l) u v =
    joinVector (gammaPrime P A B (splitVector u) (splitVector v)) := by
  unfold gammaPrime
  generalize P * B - P * A * P * A = H
  ext l
  fin_cases l <;>
    simp [Tensor.contract, joinVector, splitVector, basisVector, pairing,
      dotProduct, Matrix.mulVec, Fin.sum_univ_succ] <;> ring

lemma curvatureTerm_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q P A : ℝ → TMat} {B : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hj : ∀ᶠ r in nhds (x 0), HasDerivAt Q (A r) r ∧ Q r * P r = 1 ∧ (A r)ᵀ = A r)
    (hP : HasDerivAt P (-P (x 0) * A (x 0) * P (x 0)) (x 0))
    (hA : HasDerivAt A B (x 0)) (u v w : E3) :
    curvatureTerm g c x u v w =
      joinVector (curvatureJet (P (x 0)) (A (x 0)) B
        (splitVector u) (splitVector v) (splitVector w)) := by
  let C := christoffel g c x
  let D := fun l i j => joinVector (gammaPrime (P (x 0)) (A (x 0)) B
    (splitVector (basisVector i)) (splitVector (basisVector j))) l
  have hd (i j k d : Fin 3) := christoffel_partial_product g c hg hj hP hA i j k d
  have h0 := hj.self_of_nhds
  have hc (U V : E3) : Tensor.contract C U V =
      joinVector (gamma (P (x 0)) (A (x 0)) (splitVector U) (splitVector V)) :=
    connectionTerm_product g c hg h0.1 h0.2.1 h0.2.2 U V
  have hdc (U V : E3) : Tensor.contract D U V =
      joinVector (gammaPrime (P (x 0)) (A (x 0)) B (splitVector U) (splitVector V)) :=
    gammaPrime_contract _ _ _ _ _
  have hcurv : curvatureTerm g c x u v w =
      u 0 • Tensor.contract D v w - v 0 • Tensor.contract D u w +
        Tensor.contract C u (Tensor.contract C v w) -
        Tensor.contract C v (Tensor.contract C u w) := by
    ext l
    simp only [curvatureTerm, curvatureCoefficient, hd, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Tensor.curvature_contract C D 0 l u v w
  rw [hcurv]
  simp only [hdc, hc, split_join, curvatureJet, join_sub, join_add, join_smul]
  rfl

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

abbrev V2 := Fin 2 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def sqnorm (p : V2) : ℝ := p 0 ^ 2 + p 1 ^ 2

def qform (M : Mat2) (p : V2) : ℝ := p ⬝ᵥ (M *ᵥ p)

def d₁ (δ t : ℝ) : ℝ := 1 + δ * A t
def d₂ (δ t : ℝ) : ℝ := 1 + δ * A (1 - t)
def shear (δ t : ℝ) : ℝ := δ ^ 2 * χ t
def H (δ t : ℝ) : V2 := ![shear δ t, 1]

def P (δ t : ℝ) : Mat2 :=
  !![d₁ δ t + d₂ δ t * shear δ t ^ 2, d₂ δ t * shear δ t;
     d₂ δ t * shear δ t, d₂ δ t]

def Q (δ t : ℝ) : Mat2 := (P δ t)⁻¹

lemma P_source_formula (δ t : ℝ) :
    P δ t = d₁ δ t • vecMulVec (![1, 0] : V2) ![1, 0] +
      d₂ δ t • vecMulVec (H δ t) (H δ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, H, pow_two]

@[fun_prop] lemma d₁_smooth (δ : ℝ) : ContDiff ℝ ∞ (d₁ δ) := by
  unfold d₁
  fun_prop

@[fun_prop] lemma d₂_smooth (δ : ℝ) : ContDiff ℝ ∞ (d₂ δ) := by
  unfold d₂
  fun_prop

@[fun_prop] lemma shear_smooth (δ : ℝ) : ContDiff ℝ ∞ (shear δ) := by
  unfold shear
  fun_prop

lemma P_smooth (δ : ℝ) : ContDiff ℝ ∞ (P δ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [P] <;> fun_prop

lemma d₁_bounds {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    1 ≤ d₁ δ t ∧ d₁ δ t ≤ 2 := by
  have hA := A_nonneg ht.1
  have hA' := A_le ht.1
  dsimp [d₁]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hδ.1 hA)
  · nlinarith [hδ.2, mul_nonneg hδ.1 (by linarith [ht.2] : 0 ≤ 1 - A t)]

lemma d₂_bounds {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    1 ≤ d₂ δ t ∧ d₂ δ t ≤ 2 := by
  exact d₁_bounds hδ ⟨by linarith [ht.2], by linarith [ht.1]⟩

lemma shear_bounds {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    0 ≤ shear δ t ∧ shear δ t ≤ 1 := by
  have hc := χ_nonneg t
  have hc' := χ_le_one t
  dsimp [shear]
  constructor
  · positivity
  · calc
      δ ^ 2 * χ t ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hc' (sq_nonneg δ)
      _ ≤ 1 := by nlinarith [hδ.1, hδ.2]

lemma sqnorm_nonneg (p : V2) : 0 ≤ sqnorm p := by unfold sqnorm; positivity

lemma sqnorm_eq_zero_iff (p : V2) : sqnorm p = 0 ↔ p = 0 := by
  rw [sqnorm, add_eq_zero_iff_of_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))]
  simp only [sq_eq_zero_iff, funext_iff, Fin.forall_fin_two, Pi.zero_apply]

lemma sqnorm_pos {p : V2} (hp : p ≠ 0) : 0 < sqnorm p :=
  (sqnorm_nonneg p).lt_of_ne' (mt (sqnorm_eq_zero_iff p).mp hp)

lemma qform_P (δ t : ℝ) (p : V2) :
    qform (P δ t) p = d₁ δ t * p 0 ^ 2 + d₂ δ t * (p 1 + shear δ t * p 0) ^ 2 := by
  simp [qform, P, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

lemma shear_norm_upper (x y c : ℝ) (hc : |c| ≤ 1) :
    x ^ 2 + (y + c * x) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2) := by
  have hc' : c ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one c).mpr hc
  have hcx := mul_nonneg (sub_nonneg.mpr hc') (sq_nonneg x)
  nlinarith [sq_nonneg (y - c * x), sq_nonneg y]

lemma shear_norm_lower (x y c : ℝ) (hc : |c| ≤ 1) :
    (x ^ 2 + y ^ 2) / 3 ≤ x ^ 2 + (y + c * x) ^ 2 := by
  have h := shear_norm_upper x (y + c * x) (-c) (by simpa using hc)
  have he : y + c * x + -c * x = y := by ring
  rw [he] at h
  linarith

lemma P_elliptic {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) (p : V2) :
    sqnorm p / 3 ≤ qform (P δ t) p ∧ qform (P δ t) p ≤ 6 * sqnorm p := by
  have hd1 := d₁_bounds hδ ht
  have hd2 := d₂_bounds hδ ht
  have hc := shear_bounds (t := t) hδ
  have habs : |shear δ t| ≤ 1 := by rw [abs_of_nonneg hc.1]; exact hc.2
  have hl := shear_norm_lower (p 0) (p 1) (shear δ t) habs
  have hu := shear_norm_upper (p 0) (p 1) (shear δ t) habs
  rw [qform_P]
  change (p 0 ^ 2 + p 1 ^ 2) / 3 ≤ _ ∧ _ ≤ 6 * (p 0 ^ 2 + p 1 ^ 2)
  constructor
  · exact le_trans hl (add_le_add
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hd1.1) (sq_nonneg (p 0))])
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hd2.1) (sq_nonneg (p 1 + shear δ t * p 0))]))
  · have h1 := mul_le_mul_of_nonneg_right hd1.2 (sq_nonneg (p 0))
    have h2 := mul_le_mul_of_nonneg_right hd2.2 (sq_nonneg (p 1 + shear δ t * p 0))
    nlinarith

lemma P_hermitian (δ t : ℝ) : (P δ t).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma P_posDef {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    (P δ t).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (P_hermitian δ t)
  intro p hp
  have hl := (P_elliptic hδ ht p).1
  have hp' := sqnorm_pos hp
  change 0 < qform (P δ t) p
  linarith

lemma Q_posDef {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    (Q δ t).PosDef := (P_posDef hδ ht).inv

def u₁ (δ t : ℝ) : ℝ := δ * a t
def u₂ (δ t : ℝ) : ℝ := -δ * a (1 - t)
def v (δ t : ℝ) : ℝ := δ ^ 2 * deriv χ t
def w₁ (δ t : ℝ) : ℝ := δ * deriv a t
def w₂ (δ t : ℝ) : ℝ := δ * deriv a (1 - t)
def z (δ t : ℝ) : ℝ := δ ^ 2 * deriv (deriv χ) t

lemma d₁_hasDerivAt (δ t : ℝ) : HasDerivAt (d₁ δ) (u₁ δ t) t := by
  convert! (hasDerivAt_const t (1 : ℝ)).add ((A_hasDerivAt t).const_mul δ) using 1
  simp [u₁]

lemma d₂_hasDerivAt (δ t : ℝ) : HasDerivAt (d₂ δ) (u₂ δ t) t := by
  have h := (A_hasDerivAt (1 - t)).comp t ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  convert! (hasDerivAt_const t (1 : ℝ)).add (h.const_mul δ) using 1
  simp [u₂]

lemma shear_hasDerivAt (δ t : ℝ) : HasDerivAt (shear δ) (v δ t) t :=
  ((χ_smooth.differentiable (by simp) t).hasDerivAt).const_mul _

lemma u₁_hasDerivAt (δ t : ℝ) : HasDerivAt (u₁ δ) (w₁ δ t) t :=
  ((a_smooth.differentiable (by simp) t).hasDerivAt).const_mul _

lemma u₂_hasDerivAt (δ t : ℝ) : HasDerivAt (u₂ δ) (w₂ δ t) t := by
  have h := ((a_smooth.differentiable (by simp) (1 - t)).hasDerivAt).comp t
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  convert! h.const_mul (-δ) using 1
  simp [w₂]

lemma v_hasDerivAt (δ t : ℝ) : HasDerivAt (v δ) (z δ t) t :=
  ((χ_deriv_smooth.differentiable (by simp) t).hasDerivAt).const_mul _

def P₁ (δ t : ℝ) : Mat2 :=
  !![u₁ δ t + u₂ δ t * shear δ t ^ 2 + 2 * d₂ δ t * shear δ t * v δ t,
     u₂ δ t * shear δ t + d₂ δ t * v δ t;
     u₂ δ t * shear δ t + d₂ δ t * v δ t, u₂ δ t]

def P₂ (δ t : ℝ) : Mat2 :=
  !![w₁ δ t + w₂ δ t * shear δ t ^ 2 + 4 * u₂ δ t * shear δ t * v δ t +
       2 * d₂ δ t * v δ t ^ 2 + 2 * d₂ δ t * shear δ t * z δ t,
     w₂ δ t * shear δ t + 2 * u₂ δ t * v δ t + d₂ δ t * z δ t;
     w₂ δ t * shear δ t + 2 * u₂ δ t * v δ t + d₂ δ t * z δ t, w₂ δ t]

lemma P_hasDerivAt (δ t : ℝ) : HasDerivAt (P δ) (P₁ δ t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h1 := d₁_hasDerivAt δ t
  have h2 := d₂_hasDerivAt δ t
  have hs := shear_hasDerivAt δ t
  fin_cases i <;> fin_cases j <;> dsimp [P, P₁]
  · convert! h1.add (h2.mul (hs.pow 2)) using 1
    dsimp only [Pi.pow_apply]
    ring
  · exact (h2.mul hs)
  · exact (h2.mul hs)
  · exact h2

lemma P_deriv (δ : ℝ) : deriv (P δ) = P₁ δ := funext fun t => (P_hasDerivAt δ t).deriv

lemma P₁_hasDerivAt (δ t : ℝ) : HasDerivAt (P₁ δ) (P₂ δ t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hu1 := u₁_hasDerivAt δ t
  have hu2 := u₂_hasDerivAt δ t
  have hd2 := d₂_hasDerivAt δ t
  have hs := shear_hasDerivAt δ t
  have hv := v_hasDerivAt δ t
  fin_cases i <;> fin_cases j <;> dsimp [P₁, P₂]
  · convert! (hu1.add (hu2.mul (hs.pow 2))).add
      (((hd2.const_mul 2).mul hs).mul hv) using 1
    dsimp only [Pi.pow_apply, Pi.mul_apply]
    ring
  · convert! (hu2.mul hs).add (hd2.mul hv) using 1
    ring
  · convert! (hu2.mul hs).add (hd2.mul hv) using 1
    ring
  · exact hu2

lemma P₂_deriv (δ : ℝ) : deriv (deriv (P δ)) = P₂ δ := by
  rw [P_deriv]
  exact funext fun t => (P₁_hasDerivAt δ t).deriv

lemma Q_formula {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    Q δ t = !![1 / d₁ δ t, -shear δ t / d₁ δ t;
      -shear δ t / d₁ δ t, 1 / d₂ δ t + shear δ t ^ 2 / d₁ δ t] := by
  have h1 : d₁ δ t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (d₁_bounds hδ ht).1)
  have h2 : d₂ δ t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (d₂_bounds hδ ht).1)
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp; ring

lemma qform_Q {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) (p : V2) :
    qform (Q δ t) p = (p 0 - shear δ t * p 1) ^ 2 / d₁ δ t + p 1 ^ 2 / d₂ δ t := by
  rw [Q_formula hδ ht]
  simp [qform, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

lemma Q_elliptic {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) (p : V2) :
    sqnorm p / 6 ≤ qform (Q δ t) p ∧ qform (Q δ t) p ≤ 3 * sqnorm p := by
  have hd1 := d₁_bounds hδ ht
  have hd2 := d₂_bounds hδ ht
  have hc := shear_bounds (t := t) hδ
  have habs : |-shear δ t| ≤ 1 := by rw [abs_neg, abs_of_nonneg hc.1]; exact hc.2
  have hl := shear_norm_lower (p 1) (p 0) (-shear δ t) habs
  have hu := shear_norm_upper (p 1) (p 0) (-shear δ t) habs
  have hr1 : (1 / 2 : ℝ) ≤ (d₁ δ t)⁻¹ ∧ (d₁ δ t)⁻¹ ≤ 1 := by
    constructor
    · simpa only [one_div] using one_div_le_one_div_of_le (by linarith [hd1.1]) hd1.2
    · simpa using one_div_le_one_div_of_le zero_lt_one hd1.1
  have hr2 : (1 / 2 : ℝ) ≤ (d₂ δ t)⁻¹ ∧ (d₂ δ t)⁻¹ ≤ 1 := by
    constructor
    · simpa only [one_div] using one_div_le_one_div_of_le (by linarith [hd2.1]) hd2.2
    · simpa using one_div_le_one_div_of_le zero_lt_one hd2.1
  rw [qform_Q hδ ht]
  dsimp [sqnorm]
  rw [neg_mul, ← sub_eq_add_neg] at hl hu
  have h11 := mul_le_mul_of_nonneg_left hr1.1 (sq_nonneg (p 0 - shear δ t * p 1))
  have h12 := mul_le_mul_of_nonneg_left hr1.2 (sq_nonneg (p 0 - shear δ t * p 1))
  have h21 := mul_le_mul_of_nonneg_left hr2.1 (sq_nonneg (p 1))
  have h22 := mul_le_mul_of_nonneg_left hr2.2 (sq_nonneg (p 1))
  simp only [div_eq_mul_inv]
  constructor <;> nlinarith

def T₂ (δ : ℝ) : Mat2 := !![δ ^ 2, 1; 1, 0]
def C₂ (δ : ℝ) : Mat2 := !![0, 1; 1, -δ ^ 2]

def PEnd (δ τ : ℝ) : Mat2 := C₂ δ * P δ (1 - τ) * (C₂ δ)ᵀ

lemma frame_inverse (δ : ℝ) : C₂ δ * T₂ δ = 1 ∧ T₂ δ * C₂ δ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [T₂, C₂, Matrix.mul_apply, Fin.sum_univ_two]

lemma P_left_endpoint {δ τ : ℝ} (hτ : τ ≤ 1 / 4) :
    P δ τ = !![1 + δ * A τ, 0; 0, 1 + δ * A 1] := by
  have hc := χ_eq_zero (show τ ≤ 5 / 12 by linarith)
  have hA := A_plateau (show 2 / 3 ≤ 1 - τ by linarith) (show (2 / 3 : ℝ) ≤ 1 by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, d₁, d₂, shear, hc, hA]

lemma P_right_endpoint {δ τ : ℝ} (hτ : τ ≤ 1 / 4) :
    PEnd δ τ = !![1 + δ * A τ, 0; 0, 1 + δ * A 1] := by
  have hc := χ_eq_one (show 7 / 12 ≤ 1 - τ by linarith)
  have hA := A_plateau (show 2 / 3 ≤ 1 - τ by linarith) (show (2 / 3 : ℝ) ≤ 1 by norm_num)
  have he : 1 - (1 - τ) = τ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PEnd, C₂, P, d₁, d₂, shear, hc, hA, he,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring

def N₁ (δ t : ℝ) : Mat2 :=
  !![-δ ^ 3 * a (1 - t) * χ t ^ 2 + 2 * d₂ δ t * δ ^ 2 * χ t * deriv χ t,
      -δ * a (1 - t) * χ t + d₂ δ t * deriv χ t;
      -δ * a (1 - t) * χ t + d₂ δ t * deriv χ t, 0]

def N₂ (δ t : ℝ) : Mat2 :=
  !![δ ^ 3 * deriv a (1 - t) * χ t ^ 2 - 4 * δ ^ 3 * a (1 - t) * χ t * deriv χ t +
       2 * d₂ δ t * δ ^ 2 * deriv χ t ^ 2 +
       2 * d₂ δ t * δ ^ 2 * χ t * deriv (deriv χ) t,
      δ * deriv a (1 - t) * χ t - 2 * δ * a (1 - t) * deriv χ t +
       d₂ δ t * deriv (deriv χ) t;
      δ * deriv a (1 - t) * χ t - 2 * δ * a (1 - t) * deriv χ t +
       d₂ δ t * deriv (deriv χ) t, 0]

lemma P₁_split (δ t : ℝ) :
    P₁ δ t = diagonal ![u₁ δ t, u₂ δ t] + δ ^ 2 • N₁ δ t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P₁, N₁, shear, u₁, u₂, v] <;> ring

lemma P₂_split (δ t : ℝ) :
    P₂ δ t = diagonal ![w₁ δ t, w₂ δ t] + δ ^ 2 • N₂ δ t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P₂, N₂, shear, w₁, w₂, u₂, v, z] <;> ring

@[fun_prop] lemma a_deriv_smooth : ContDiff ℝ ∞ (deriv a) :=
  (contDiff_infty_iff_deriv.mp a_smooth).2

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

lemma N₁_smooth : ContDiff ℝ ∞ (fun y : ℝ × ℝ => N₁ y.1 y.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [N₁, d₂] <;> fun_prop

lemma N₂_smooth : ContDiff ℝ ∞ (fun y : ℝ × ℝ => N₂ y.1 y.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [N₂, d₂] <;> fun_prop

lemma normalized_errors_bounded : ∃ B : ℝ, 1 ≤ B ∧
    ∀ δ ∈ Icc (0 : ℝ) (1 / 2), ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j,
      |N₁ δ t i j| ≤ B ∧ |N₂ δ t i j| ≤ B := by
  obtain ⟨b1, hb1⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (1 / 2) ×ˢ Icc (0 : ℝ) 1) N₁_smooth.continuous.continuousOn
  obtain ⟨b2, hb2⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (1 / 2) ×ˢ Icc (0 : ℝ) 1) N₂_smooth.continuous.continuousOn
  refine ⟨max 1 (max b1 b2), le_max_left _ _, ?_⟩
  intro δ hδ t ht i j
  constructor
  · calc
      |N₁ δ t i j| ≤ ‖N₁ δ t i‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (N₁ δ t i) j
      _ ≤ ‖N₁ δ t‖ := norm_le_pi_norm _ i
      _ ≤ b1 := hb1 (δ, t) ⟨hδ, ht⟩
      _ ≤ max 1 (max b1 b2) := le_trans (le_max_left _ _) (le_max_right _ _)
  · calc
      |N₂ δ t i j| ≤ ‖N₂ δ t i‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (N₂ δ t i) j
      _ ≤ ‖N₂ δ t‖ := norm_le_pi_norm _ i
      _ ≤ b2 := hb2 (δ, t) ⟨hδ, ht⟩
      _ ≤ max 1 (max b1 b2) := le_trans (le_max_right _ _) (le_max_right _ _)

lemma sqnorm_add_le (p q : V2) :
    sqnorm (p + q) ≤ 2 * sqnorm p + 2 * sqnorm q := by
  simp only [sqnorm, Pi.add_apply]
  nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]

lemma sqnorm_smul (r : ℝ) (p : V2) : sqnorm (r • p) = r ^ 2 * sqnorm p := by
  simp only [sqnorm, Pi.smul_apply, smul_eq_mul]
  ring

lemma qform_add (M N : Mat2) (p : V2) :
    qform (M + N) p = qform M p + qform N p := by
  simp only [qform, Matrix.add_mulVec, dotProduct_add]

lemma qform_smul (r : ℝ) (M : Mat2) (p : V2) :
    qform (r • M) p = r * qform M p := by
  simp only [qform, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma qform_neg (M : Mat2) (p : V2) : qform (-M) p = -qform M p := by
  simp only [qform, Matrix.neg_mulVec, dotProduct_neg]

lemma qform_diag (r s : ℝ) (p : V2) :
    qform (diagonal ![r, s]) p = r * p 0 ^ 2 + s * p 1 ^ 2 := by
  simp [qform, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

lemma dotProduct_sq_le (p q : V2) : (p ⬝ᵥ q) ^ 2 ≤ sqnorm p * sqnorm q := by
  simp only [dotProduct, Fin.sum_univ_two, sqnorm]
  nlinarith [sq_nonneg (p 0 * q 1 - p 1 * q 0)]

lemma sq_le_of_abs_le {x B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) : x ^ 2 ≤ B ^ 2 := by
  have h := (sq_le_sq₀ (abs_nonneg x) hB).mpr hx
  simpa only [sq_abs] using h

lemma sqnorm_mulVec_le {M : Mat2} {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i j, |M i j| ≤ B) (p : V2) :
    sqnorm (M *ᵥ p) ≤ 4 * B ^ 2 * sqnorm p := by
  have h0 := dotProduct_sq_le (M 0) p
  have h1 := dotProduct_sq_le (M 1) p
  have h00 := sq_le_of_abs_le hB (hM 0 0)
  have h01 := sq_le_of_abs_le hB (hM 0 1)
  have h10 := sq_le_of_abs_le hB (hM 1 0)
  have h11 := sq_le_of_abs_le hB (hM 1 1)
  have hm0 := mul_le_mul_of_nonneg_right (add_le_add h00 h01) (sqnorm_nonneg p)
  have hm1 := mul_le_mul_of_nonneg_right (add_le_add h10 h11) (sqnorm_nonneg p)
  change (M 0 ⬝ᵥ p) ^ 2 + (M 1 ⬝ᵥ p) ^ 2 ≤ _
  dsimp only [sqnorm] at h0 h1 hm0 hm1 ⊢
  nlinarith

lemma abs_qform_le {M : Mat2} {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i j, |M i j| ≤ B) (p : V2) :
    |qform M p| ≤ 2 * B * sqnorm p := by
  have h := dotProduct_sq_le p (M *ᵥ p)
  have hm := mul_le_mul_of_nonneg_left (sqnorm_mulVec_le hB hM p) (sqnorm_nonneg p)
  change qform M p ^ 2 ≤ _ at h
  have ht : 0 ≤ 2 * B * sqnorm p := mul_nonneg (mul_nonneg (by norm_num) hB) (sqnorm_nonneg p)
  have ha := abs_nonneg (qform M p)
  have hs := sq_abs (qform M p)
  nlinarith

def cutoffMargin : ℝ := 144 * Real.exp (-12)

lemma cutoffMargin_pos : 0 < cutoffMargin := by
  unfold cutoffMargin
  positivity

lemma middle_concavity {δ t B : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (ht : t ∈ Icc (5 / 12) (7 / 12))
    (hN : ∀ i j, |N₂ δ t i j| ≤ B) (hsmall : 4 * B * δ ≤ cutoffMargin)
    (p : V2) :
    cutoffMargin * δ / 2 * sqnorm p ≤ qform (-P₂ δ t) p := by
  have ha := a_slope_lower ht
  have hb := a_slope_lower (u := 1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  change cutoffMargin ≤ -deriv a t at ha
  change cutoffMargin ≤ -deriv a (1 - t) at hb
  have ha' := mul_le_mul_of_nonneg_right ha (mul_nonneg hδ (sq_nonneg (p 0)))
  have hb' := mul_le_mul_of_nonneg_right hb (mul_nonneg hδ (sq_nonneg (p 1)))
  have hn := (abs_le.mp (abs_qform_le hB hN p)).2
  have hn' := mul_le_mul_of_nonneg_left hn (sq_nonneg δ)
  have hs := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hδ (sqnorm_nonneg p))
  rw [qform_neg, P₂_split, qform_add, qform_diag, qform_smul]
  dsimp only [w₁, w₂, sqnorm] at ha' hb' hn' hs ⊢
  nlinarith

lemma a_sq_le_one (t : ℝ) : a t ^ 2 ≤ 1 := by
  nlinarith [a_nonneg t, a_lt_one t]

lemma diagonal_first_bound (δ t : ℝ) (p : V2) :
    sqnorm ((diagonal ![u₁ δ t, u₂ δ t]) *ᵥ p) ≤ δ ^ 2 * sqnorm p := by
  have ha := mul_le_mul_of_nonneg_right (a_sq_le_one t)
    (mul_nonneg (sq_nonneg δ) (sq_nonneg (p 0)))
  have hb := mul_le_mul_of_nonneg_right (a_sq_le_one (1 - t))
    (mul_nonneg (sq_nonneg δ) (sq_nonneg (p 1)))
  simp [sqnorm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, u₁, u₂]
  nlinarith

lemma first_derivative_bound {δ t B : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hB : 0 ≤ B)
    (hN : ∀ i j, |N₁ δ t i j| ≤ B) (p : V2) :
    sqnorm (P₁ δ t *ᵥ p) ≤ (2 + 8 * B ^ 2) * δ ^ 2 * sqnorm p := by
  have hd := diagonal_first_bound δ t p
  have hn := sqnorm_mulVec_le hB hN p
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith [hδ.1, hδ.2]
  have hδ4 : (δ ^ 2) ^ 2 ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]
  have hn' := mul_le_mul_of_nonneg_left hn (sq_nonneg (δ ^ 2))
  have he := mul_le_mul_of_nonneg_right hδ4
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg B)) (sqnorm_nonneg p))
  rw [P₁_split, Matrix.add_mulVec, Matrix.smul_mulVec]
  have hs := sqnorm_add_le ((diagonal ![u₁ δ t, u₂ δ t]) *ᵥ p)
    (δ ^ 2 • (N₁ δ t *ᵥ p))
  rw [sqnorm_smul] at hs
  nlinarith

lemma middle_domination {δ t B : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hB : 0 ≤ B)
    (ht : t ∈ Icc (5 / 12) (7 / 12))
    (hN : ∀ i j, |N₁ δ t i j| ≤ B ∧ |N₂ δ t i j| ≤ B)
    (hsmall : 4 * B * δ ≤ cutoffMargin) (p : V2) :
    0 ≤ qform (-P₂ δ t) p ∧
    sqnorm (P₁ δ t *ᵥ p) ≤
      (2 * (2 + 8 * B ^ 2) / cutoffMargin) * δ * qform (-P₂ δ t) p := by
  have hc := middle_concavity hδ.1 hB ht (fun i j => (hN i j).2) hsmall p
  have hp := first_derivative_bound hδ hB (fun i j => (hN i j).1) p
  have hm := cutoffMargin_pos
  constructor
  · exact le_trans (mul_nonneg (div_nonneg (mul_nonneg hm.le hδ.1) (by norm_num))
      (sqnorm_nonneg p)) hc
  · have hmul := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ (2 * (2 + 8 * B ^ 2) / cutoffMargin) * δ by positivity [hδ.1])
    calc
      sqnorm (P₁ δ t *ᵥ p) ≤ (2 + 8 * B ^ 2) * δ ^ 2 * sqnorm p := hp
      _ = (2 * (2 + 8 * B ^ 2) / cutoffMargin) * δ *
          (cutoffMargin * δ / 2 * sqnorm p) := by field_simp
      _ ≤ _ := hmul

lemma outside_cutoff_derivatives {t : ℝ} (ht : t ∉ Icc (5 / 12) (7 / 12)) :
    deriv χ t = 0 ∧ deriv (deriv χ) t = 0 := by
  have h : t < 5 / 12 ∨ 7 / 12 < t := by
    simpa only [mem_Icc, not_and_or, not_le] using ht
  rcases h with hl | hr
  · exact ⟨χ_deriv_left hl, χ_deriv2_left hl⟩
  · exact ⟨χ_deriv_right hr, χ_deriv2_right hr⟩

lemma stationary_first_formula {δ t : ℝ} (hχ : deriv χ t = 0) (p : V2) :
    sqnorm (P₁ δ t *ᵥ p) =
      (δ * a t * p 0 + shear δ t * (-δ * a (1 - t) * (p 1 + shear δ t * p 0))) ^ 2 +
      (-δ * a (1 - t) * (p 1 + shear δ t * p 0)) ^ 2 := by
  simp [sqnorm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, P₁, u₁, u₂, v, hχ]
  ring

lemma stationary_second_formula {δ t : ℝ}
    (hχ : deriv χ t = 0) (hχ' : deriv (deriv χ) t = 0) (p : V2) :
    qform (-P₂ δ t) p = δ *
      (-deriv a t * p 0 ^ 2 - deriv a (1 - t) * (p 1 + shear δ t * p 0) ^ 2) := by
  simp [qform, Matrix.mulVec, dotProduct, Fin.sum_univ_two, P₂, w₁, w₂, v, z, hχ, hχ']
  ring

lemma outside_domination {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1)
    (hout : t ∉ Icc (5 / 12) (7 / 12)) (p : V2) :
    0 ≤ qform (-P₂ δ t) p ∧
    sqnorm (P₁ δ t *ᵥ p) ≤ 3 * δ * qform (-P₂ δ t) p := by
  obtain ⟨hc, hc'⟩ := outside_cutoff_derivatives hout
  have hshear := shear_bounds (t := t) hδ
  have hsabs : |shear δ t| ≤ 1 := by rw [abs_of_nonneg hshear.1]; exact hshear.2
  have hn := shear_norm_upper (-δ * a (1 - t) * (p 1 + shear δ t * p 0))
    (δ * a t * p 0) (shear δ t) hsabs
  have ha := a_sq_le_neg_deriv ht
  have hb := a_sq_le_neg_deriv (u := 1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hm1 := mul_le_mul_of_nonneg_right ha (mul_nonneg (sq_nonneg δ) (sq_nonneg (p 0)))
  have hm2 := mul_le_mul_of_nonneg_right hb
    (mul_nonneg (sq_nonneg δ) (sq_nonneg (p 1 + shear δ t * p 0)))
  rw [stationary_second_formula hc hc', stationary_first_formula hc]
  constructor
  · apply mul_nonneg hδ.1
    have h1 : 0 ≤ -deriv a t * p 0 ^ 2 :=
      mul_nonneg (neg_nonneg.mpr (a_deriv_nonpos t)) (sq_nonneg (p 0))
    have h2 : 0 ≤ -deriv a (1 - t) * (p 1 + shear δ t * p 0) ^ 2 :=
      mul_nonneg (neg_nonneg.mpr (a_deriv_nonpos (1 - t)))
        (sq_nonneg (p 1 + shear δ t * p 0))
    linarith
  · nlinarith

theorem uniform_original_bounds : ∃ δ₀ C : ℝ,
    0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ 0 < C ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀, ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : V2,
      (sqnorm p / 3 ≤ qform (P δ t) p ∧ qform (P δ t) p ≤ 6 * sqnorm p) ∧
      (sqnorm p / 6 ≤ qform (Q δ t) p ∧ qform (Q δ t) p ≤ 3 * sqnorm p) ∧
      sqnorm (deriv (P δ) t *ᵥ p) ≤ C ^ 2 * δ ^ 2 * sqnorm p ∧
      0 ≤ qform (-deriv (deriv (P δ)) t) p ∧
      sqnorm (deriv (P δ) t *ᵥ p) ≤ C * δ * qform (-deriv (deriv (P δ)) t) p := by
  obtain ⟨B, hB, hN⟩ := normalized_errors_bounded
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hm := cutoffMargin_pos
  let δ₀ := min (1 / 2 : ℝ) (cutoffMargin / (4 * B))
  let K := 2 + 8 * B ^ 2
  let C := max 3 (max K (2 * K / cutoffMargin))
  have hδ₀ : 0 < δ₀ := lt_min (by norm_num) (div_pos hm (by positivity))
  have hC3 : 3 ≤ C := le_max_left _ _
  have hCK : K ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCM : 2 * K / cutoffMargin ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hKC : K ≤ C ^ 2 := by nlinarith
  refine ⟨δ₀, C, hδ₀, min_le_left _ _, by linarith, ?_⟩
  intro δ hδ t ht p
  have hδ' : δ ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨hδ.1.le, le_trans hδ.2 (min_le_left _ _)⟩
  have hsmall : 4 * B * δ ≤ cutoffMargin := by
    have h := le_trans hδ.2 (min_le_right _ _)
    have hd : 0 < 4 * B := by positivity
    simpa only [mul_comm] using (le_div_iff₀ hd).mp h
  refine ⟨P_elliptic hδ' ht p, Q_elliptic hδ' ht p, ?_⟩
  rw [P₂_deriv, P_deriv]
  constructor
  · calc
      sqnorm (P₁ δ t *ᵥ p) ≤ K * δ ^ 2 * sqnorm p :=
        first_derivative_bound hδ' hB0.le (fun i j => (hN δ hδ' t ht i j).1) p
      _ ≤ C ^ 2 * δ ^ 2 * sqnorm p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC (sq_nonneg δ))
          (sqnorm_nonneg p)
  · by_cases hmid : t ∈ Icc (5 / 12) (7 / 12)
    · obtain ⟨hc, hd⟩ := middle_domination hδ' hB0.le hmid (hN δ hδ' t ht) hsmall p
      refine ⟨hc, hd.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM hδ.1.le) hc
    · obtain ⟨hc, hd⟩ := outside_domination hδ' ht hmid p
      refine ⟨hc, hd.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hδ.1.le) hc

def congruenceCLM (C : Mat2) : Mat2 →L[ℝ] Mat2 :=
  ((mulRightLinearMap (Fin 2) ℝ Cᵀ).comp
    (mulLeftLinearMap (Fin 2) ℝ C)).toContinuousLinearMap

lemma congruenceCLM_apply (C M : Mat2) : congruenceCLM C M = C * M * Cᵀ := rfl

lemma qform_congruence (C M : Mat2) (p : V2) :
    qform (C * M * Cᵀ) p = qform M (Cᵀ *ᵥ p) := by
  simp [qform, dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma C₂_transpose (δ : ℝ) : (C₂ δ)ᵀ = C₂ δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma T₂_transpose (δ : ℝ) : (T₂ δ)ᵀ = T₂ δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma C₂_norm_bounds {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (p : V2) :
    sqnorm p / 3 ≤ sqnorm (C₂ δ *ᵥ p) ∧ sqnorm (C₂ δ *ᵥ p) ≤ 3 * sqnorm p := by
  have h : |-(δ ^ 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg δ)]
    nlinarith [hδ.1, hδ.2]
  have hl := shear_norm_lower (p 1) (p 0) (-(δ ^ 2)) h
  have hu := shear_norm_upper (p 1) (p 0) (-(δ ^ 2)) h
  simp [sqnorm, C₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor <;> nlinarith

lemma T₂_norm_bounds {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (p : V2) :
    sqnorm p / 3 ≤ sqnorm (T₂ δ *ᵥ p) ∧ sqnorm (T₂ δ *ᵥ p) ≤ 3 * sqnorm p := by
  have h : |δ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg δ)]
    nlinarith [hδ.1, hδ.2]
  have hl := shear_norm_lower (p 0) (p 1) (δ ^ 2) h
  have hu := shear_norm_upper (p 0) (p 1) (δ ^ 2) h
  simp [sqnorm, T₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor <;> nlinarith

lemma PEnd_hasDerivAt (δ τ : ℝ) :
    HasDerivAt (PEnd δ) (-(C₂ δ * P₁ δ (1 - τ) * (C₂ δ)ᵀ)) τ := by
  have hd := (P_hasDerivAt δ (1 - τ)).scomp τ
    ((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id τ))
  have hc := (congruenceCLM (C₂ δ)).hasFDerivAt.comp_hasDerivAt τ hd
  change HasDerivAt (fun x => C₂ δ * P δ (1 - x) * (C₂ δ)ᵀ)
    (C₂ δ * ((0 - 1 : ℝ) • P₁ δ (1 - τ)) * (C₂ δ)ᵀ) τ at hc
  convert! hc using 1
  simp

lemma PEnd_deriv (δ : ℝ) : deriv (PEnd δ) =
    fun τ => -(C₂ δ * P₁ δ (1 - τ) * (C₂ δ)ᵀ) :=
  funext fun τ => (PEnd_hasDerivAt δ τ).deriv

lemma PEnd_deriv₂ (δ : ℝ) : deriv (deriv (PEnd δ)) =
    fun τ => C₂ δ * P₂ δ (1 - τ) * (C₂ δ)ᵀ := by
  rw [PEnd_deriv]
  funext τ
  have hd := (P₁_hasDerivAt δ (1 - τ)).scomp τ
    ((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id τ))
  have hc := ((congruenceCLM (C₂ δ)).hasFDerivAt.comp_hasDerivAt τ hd).neg
  change HasDerivAt (fun x => -(C₂ δ * P₁ δ (1 - x) * (C₂ δ)ᵀ))
    (-(C₂ δ * ((0 - 1 : ℝ) • P₂ δ (1 - τ)) * (C₂ δ)ᵀ)) τ at hc
  have he : HasDerivAt (fun τ => -(C₂ δ * P₁ δ (1 - τ) * (C₂ δ)ᵀ))
      (C₂ δ * P₂ δ (1 - τ) * (C₂ δ)ᵀ) τ := by
    simpa only [zero_sub,
      neg_smul, one_smul, Matrix.mul_neg, Matrix.neg_mul, neg_neg] using hc
  exact he.deriv

lemma QEnd_formula {δ τ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hτ : τ ∈ Icc 0 1) :
    (PEnd δ τ)⁻¹ = T₂ δ * Q δ (1 - τ) * (T₂ δ)ᵀ := by
  have ht : 1 - τ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  apply Matrix.inv_eq_left_inv
  dsimp only [PEnd, Q]
  rw [T₂_transpose, C₂_transpose]
  calc
    (T₂ δ * (P δ (1 - τ))⁻¹ * T₂ δ) * (C₂ δ * P δ (1 - τ) * C₂ δ) =
        T₂ δ * ((P δ (1 - τ))⁻¹ * P δ (1 - τ)) * C₂ δ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (T₂ δ) (C₂ δ), (frame_inverse δ).2,
        Matrix.one_mul]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (P_posDef hδ ht).det_pos.ne'), Matrix.mul_one, (frame_inverse δ).2]

lemma PEnd_elliptic {δ τ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hτ : τ ∈ Icc 0 1) (p : V2) :
    sqnorm p / 9 ≤ qform (PEnd δ τ) p ∧ qform (PEnd δ τ) p ≤ 18 * sqnorm p := by
  have ht : 1 - τ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hp := P_elliptic hδ ht (C₂ δ *ᵥ p)
  have hc := C₂_norm_bounds hδ p
  rw [PEnd, qform_congruence, C₂_transpose]
  constructor <;> linarith [hp.1, hp.2, hc.1, hc.2]

lemma QEnd_elliptic {δ τ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hτ : τ ∈ Icc 0 1) (p : V2) :
    sqnorm p / 18 ≤ qform (PEnd δ τ)⁻¹ p ∧ qform (PEnd δ τ)⁻¹ p ≤ 9 * sqnorm p := by
  have ht : 1 - τ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hq := Q_elliptic hδ ht (T₂ δ *ᵥ p)
  have hc := T₂_norm_bounds hδ p
  rw [QEnd_formula hδ hτ, qform_congruence, T₂_transpose]
  constructor <;> linarith [hq.1, hq.2, hc.1, hc.2]

lemma sqnorm_neg (p : V2) : sqnorm (-p) = sqnorm p := by simp [sqnorm]

lemma PEnd_derivative_norm {δ τ : ℝ} (p : V2) :
    sqnorm (deriv (PEnd δ) τ *ᵥ p) =
      sqnorm (C₂ δ *ᵥ (P₁ δ (1 - τ) *ᵥ (C₂ δ *ᵥ p))) := by
  rw [PEnd_deriv, Matrix.neg_mulVec, sqnorm_neg, C₂_transpose]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

lemma PEnd_derivative_qform (δ τ : ℝ) (p : V2) :
    qform (-deriv (deriv (PEnd δ)) τ) p = qform (-P₂ δ (1 - τ)) (C₂ δ *ᵥ p) := by
  rw [PEnd_deriv₂]
  change qform (-(C₂ δ * P₂ δ (1 - τ) * (C₂ δ)ᵀ)) p = _
  rw [qform_neg, qform_congruence, C₂_transpose, qform_neg]

lemma PEnd_derivative_bounds {δ τ C : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (hd : ∀ q, sqnorm (P₁ δ (1 - τ) *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q)
    (hc : ∀ q, 0 ≤ qform (-P₂ δ (1 - τ)) q)
    (hdom : ∀ q, sqnorm (P₁ δ (1 - τ) *ᵥ q) ≤ C * δ * qform (-P₂ δ (1 - τ)) q)
    (p : V2) :
    sqnorm (deriv (PEnd δ) τ *ᵥ p) ≤ (3 * C) ^ 2 * δ ^ 2 * sqnorm p ∧
    0 ≤ qform (-deriv (deriv (PEnd δ)) τ) p ∧
    sqnorm (deriv (PEnd δ) τ *ᵥ p) ≤
      (3 * C) * δ * qform (-deriv (deriv (PEnd δ)) τ) p := by
  rw [PEnd_derivative_norm, PEnd_derivative_qform]
  have h₁ := (C₂_norm_bounds hδ (P₁ δ (1 - τ) *ᵥ (C₂ δ *ᵥ p))).2
  have h₂ := (C₂_norm_bounds hδ p).2
  have h₃ := mul_le_mul_of_nonneg_left h₂ (mul_nonneg (sq_nonneg C) (sq_nonneg δ))
  refine ⟨?_, hc _, ?_⟩
  · nlinarith [hd (C₂ δ *ᵥ p)]
  · nlinarith [hdom (C₂ δ *ᵥ p)]

def coordinateCometric (right : Bool) (δ : ℝ) : ℝ → Mat2 :=
  if right then PEnd δ else P δ

theorem uniform_cometric_bounds : ∃ δ₀ C : ℝ,
    0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ 0 < C ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀, ∀ right : Bool, ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : V2,
      let R := coordinateCometric right δ
      (sqnorm p / 9 ≤ qform (R t) p ∧ qform (R t) p ≤ 18 * sqnorm p) ∧
      (sqnorm p / 18 ≤ qform (R t)⁻¹ p ∧ qform (R t)⁻¹ p ≤ 9 * sqnorm p) ∧
      sqnorm (deriv R t *ᵥ p) ≤ C ^ 2 * δ ^ 2 * sqnorm p ∧
      0 ≤ qform (-deriv (deriv R) t) p ∧
      sqnorm (deriv R t *ᵥ p) ≤ C * δ * qform (-deriv (deriv R) t) p := by
  obtain ⟨δ₀, C, hδ₀, hδ₀', hC, h⟩ := uniform_original_bounds
  refine ⟨δ₀, 3 * C, hδ₀, hδ₀', by positivity, ?_⟩
  intro δ hδ right t ht p
  have hδ' : δ ∈ Icc (0 : ℝ) (1 / 2) := ⟨hδ.1.le, le_trans hδ.2 hδ₀'⟩
  cases right with
  | false =>
    simp only [coordinateCometric, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hp, hq, hd, hc, hdom⟩ := h δ hδ t ht p
    have hn := sqnorm_nonneg p
    refine ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩,
      ⟨by change sqnorm p / 18 ≤ qform (Q δ t) p; linarith [hq.1],
        by change qform (Q δ t) p ≤ 9 * sqnorm p; linarith [hq.2]⟩, ?_, hc, ?_⟩
    · have he := mul_nonneg (sq_nonneg C) (mul_nonneg (sq_nonneg δ) hn)
      nlinarith
    · have he := mul_nonneg (mul_nonneg hC.le hδ.1.le) hc
      nlinarith
  | true =>
    simp only [coordinateCometric, ↓reduceIte]
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h' := fun q => (h δ hδ (1 - t) ht' q).2.2
    rw [P₂_deriv, P_deriv] at h'
    exact ⟨PEnd_elliptic hδ' ht p, QEnd_elliptic hδ' ht p,
      PEnd_derivative_bounds hδ' (fun q => (h' q).1) (fun q => (h' q).2.1)
        (fun q => (h' q).2.2) p⟩

lemma sqnorm_eq_euclidean (p : V2) :
    sqnorm p = ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, sqnorm, Fin.sum_univ_two, Real.norm_eq_abs]

def euclideanOperator (M : Mat2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  M.toEuclideanLin.toContinuousLinearMap

lemma euclideanOperator_apply (M : Mat2) (p : EuclideanSpace ℝ (Fin 2)) :
    euclideanOperator M p = WithLp.toLp 2 (M *ᵥ p.ofLp) := by
  rfl

lemma operator_norm_of_sqnorm (M : Mat2) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ p : V2, sqnorm (M *ᵥ p) ≤ K ^ 2 * sqnorm p) :
    ‖euclideanOperator M‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro p
  have hp := h p.ofLp
  rw [sqnorm_eq_euclidean, sqnorm_eq_euclidean, WithLp.toLp_ofLp] at hp
  rw [euclideanOperator_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg p))).mp
  simpa only [mul_pow] using hp

theorem uniform_cometric_operator_bound : ∃ δ₀ C : ℝ,
    0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ 0 < C ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀, ∀ right : Bool, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖euclideanOperator (deriv (coordinateCometric right δ) t)‖ ≤ C * δ := by
  obtain ⟨δ₀, C, hδ₀, hδ₀', hC, h⟩ := uniform_cometric_bounds
  refine ⟨δ₀, C, hδ₀, hδ₀', hC, ?_⟩
  intro δ hδ right t ht
  apply operator_norm_of_sqnorm _ (mul_nonneg hC.le hδ.1.le)
  intro p
  simpa only [mul_pow, mul_assoc] using (h δ hδ right t ht p).2.2.1

end ThreeManifold.Cometric

namespace ThreeManifold.LocalNeck

section
open Manifold Bundle Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

abbrev Slab := {x : E3 // x 0 ∈ Ioo (0 : ℝ) 1}

instance : Nonempty Slab := ⟨⟨fun _ => 1 / 2, by norm_num⟩⟩

lemma slab_isOpen : IsOpen {x : E3 | x 0 ∈ Ioo (0 : ℝ) 1} :=
  isOpen_Ioo.preimage (continuous_apply 0)

theorem slabEmbedding : Topology.IsOpenEmbedding (Subtype.val : Slab → E3) :=
  slab_isOpen.isOpenEmbedding_subtypeVal

def slabChart : OpenPartialHomeomorph Slab E3 :=
  slabEmbedding.toOpenPartialHomeomorph Subtype.val

@[simp] lemma slabChart_source : slabChart.source = univ := by
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source _ _

@[simp] lemma slabChart_apply (x : Slab) : slabChart x = x.val := rfl

instance : ChartedSpace E3 Slab := slabChart.singletonChartedSpace slabChart_source
instance : IsManifold I3 ∞ Slab := slabChart.isManifold_singleton slabChart_source

@[simp] lemma chartAt_eq (x : Slab) : chartAt E3 x = slabChart := rfl

lemma achart_eq (x y : Slab) : achart E3 x = achart E3 y := by
  apply Subtype.ext
  rfl

@[simp] lemma slab_symmL (b b' : Slab) :
    (trivializationAt E3 (TangentSpace I3) b).symmL ℝ b' = (1 : E3 →L[ℝ] E3) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core]
  · rw [achart_eq b b']
    apply ContinuousLinearMap.ext
    intro v
    apply (tangentBundleCore I3 Slab).coordChange_self
    simp
  · simp

@[simp] lemma slab_linearMapAt (b b' : Slab) :
    (trivializationAt E3 (TangentSpace I3) b).continuousLinearMapAt ℝ b' =
      (1 : E3 →L[ℝ] E3) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core]
  · rw [achart_eq b b']
    apply ContinuousLinearMap.ext
    intro v
    apply (tangentBundleCore I3 Slab).coordChange_self
    simp
  · simp

lemma slab_val_smooth : ContMDiff I3 I3 ∞ (Subtype.val : Slab → E3) := by
  intro x
  convert! contMDiffAt_extChartAt (I := I3) (n := ∞) (x := x) using 1

open Cometric Neck

lemma Q_formula_of_ne {δ t : ℝ} (h1 : d₁ δ t ≠ 0) (h2 : d₂ δ t ≠ 0) :
    Q δ t = !![1 / d₁ δ t, -shear δ t / d₁ δ t;
      -shear δ t / d₁ δ t, 1 / d₂ δ t + shear δ t ^ 2 / d₁ δ t] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp; ring

lemma Q_smoothAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    ContDiffAt ℝ ∞ (Q δ) t := by
  have h1 : d₁ δ t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (d₁_bounds hδ ht).1)
  have h2 : d₂ δ t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (d₂_bounds hδ ht).1)
  have hformula : Q δ =ᶠ[nhds t] fun r =>
      !![1 / d₁ δ r, -shear δ r / d₁ δ r;
        -shear δ r / d₁ δ r, 1 / d₂ δ r + shear δ r ^ 2 / d₁ δ r] := by
    filter_upwards [(d₁_smooth δ).continuous.continuousAt.eventually_ne h1,
      (d₂_smooth δ).continuous.continuousAt.eventually_ne h2] with r hr1 hr2
    exact Q_formula_of_ne hr1 hr2
  apply ContDiffAt.congr_of_eventuallyEq (f := fun r =>
      !![1 / d₁ δ r, -shear δ r / d₁ δ r;
        -shear δ r / d₁ δ r, 1 / d₂ δ r + shear δ r ^ 2 / d₁ δ r]) _ hformula
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop

def metricBilin (q : Matrix (Fin 3) (Fin 3) ℝ) : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
  ∑ i, ∑ j, q i j • (ContinuousLinearMap.proj i : E3 →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj j : E3 →L[ℝ] ℝ)

lemma metricBilin_apply (q : Matrix (Fin 3) (Fin 3) ℝ) (u v : E3) :
    metricBilin q u v = ∑ i, ∑ j, u i * q i j * v j := by
  simp only [metricBilin, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 1
  funext i
  congr 1
  funext j
  ring

lemma metricBilin_smooth : ContDiff ℝ ∞ metricBilin := by
  have : IsBoundedSMul ℝ (E3 →L[ℝ] E3 →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (E3 →L[ℝ] E3 →L[ℝ] ℝ) _ _ _
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 3 → ℝ) i)).smul
    (contDiff_const (c := (ContinuousLinearMap.proj i : E3 →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj j : E3 →L[ℝ] ℝ)))

lemma metricBilin_block (q : Mat2) (u v : E3) :
    metricBilin (blockMatrix q) u v = metric q (splitVector u) (splitVector v) := by
  simp [metricBilin_apply, blockMatrix, metric, splitVector, pairing, dotProduct,
    Matrix.mulVec, Fin.sum_univ_succ]
  ring

lemma blockMatrix_smooth : ContDiff ℝ ∞ (blockMatrix : Mat2 → Matrix (Fin 3) (Fin 3) ℝ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · change ContDiff ℝ ∞ (fun _ : Mat2 => (1 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun _ : Mat2 => (0 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun _ : Mat2 => (0 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun _ : Mat2 => (0 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun q : Mat2 => q 0 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun q : Mat2 => q 0 1)
    fun_prop
  · change ContDiff ℝ ∞ (fun _ : Mat2 => (0 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun q : Mat2 => q 1 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun q : Mat2 => q 1 1)
    fun_prop

lemma neckBilin_lower {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1)
    (u : E3) :
    (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) / 6 ≤ metricBilin (blockMatrix (Q δ t)) u u := by
  rw [metricBilin_block]
  change _ ≤ u 0 * u 0 + qform (Q δ t) ![u 1, u 2]
  have h := (Q_elliptic hδ ht ![u 1, u 2]).1
  simp only [sqnorm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  nlinarith [sq_nonneg (u 0)]

lemma neckBilin_pos {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1)
    (u : E3) (hu : u ≠ 0) : 0 < metricBilin (blockMatrix (Q δ t)) u u := by
  have hp : 0 < u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
    by_contra h
    have hsum : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 ≤ 0 := le_of_not_gt h
    have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
    have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
    have h2 : u 2 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
    apply hu
    ext i
    fin_cases i <;> assumption
  exact lt_of_lt_of_le (div_pos hp (by norm_num)) (neckBilin_lower hδ ht u)

lemma neckBilin_symm {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1)
    (u v : E3) : metricBilin (blockMatrix (Q δ t)) u v =
      metricBilin (blockMatrix (Q δ t)) v u := by
  rw [metricBilin_block, metricBilin_block]
  apply metric_symm
  exact Matrix.isHermitian_iff_isSymm.mp (Q_posDef hδ ht).isHermitian

lemma neckBilin_bounded {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    Bornology.IsVonNBounded ℝ {u : E3 | metricBilin (blockMatrix (Q δ t)) u u < 1} := by
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  refine ⟨3, fun u hu => ?_⟩
  have hl := neckBilin_lower hδ ht u
  change metricBilin (blockMatrix (Q δ t)) u u < 1 at hu
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  fin_cases i <;> dsimp <;> constructor <;>
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]

lemma neckBilin_smooth {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    ContMDiff I3 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ) ∞
      (fun x : Slab => metricBilin (blockMatrix (Q δ (x.val 0)))) := by
  intro x
  have ht : x.val 0 ∈ Icc (0 : ℝ) 1 := ⟨x.property.1.le, x.property.2.le⟩
  have hf : ContDiffAt ℝ ∞ (fun r => metricBilin (blockMatrix (Q δ r))) (x.val 0) :=
    metricBilin_smooth.contDiffAt.comp (x.val 0)
      (blockMatrix_smooth.contDiffAt.comp (x.val 0) (Q_smoothAt hδ ht))
  have hv : ContMDiffAt I3 𝓘(ℝ, ℝ) ∞ (fun y : Slab => y.val 0) x :=
    ((contDiff_apply ℝ ℝ (0 : Fin 3)).contMDiff.comp slab_val_smooth).contMDiffAt
  have hfM : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ) ∞
      (fun r => metricBilin (blockMatrix (Q δ r))) (x.val 0) := hf.contMDiffAt
  exact hfM.comp (f := fun y : Slab => y.val 0) x hv

def neckMetric {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) : SmoothMetric Slab where
  inner x := metricBilin (blockMatrix (Q δ (x.val 0)))
  symm x u v := neckBilin_symm hδ ⟨x.property.1.le, x.property.2.le⟩ u v
  pos x u hu := neckBilin_pos hδ ⟨x.property.1.le, x.property.2.le⟩ u hu
  isVonNBounded x := neckBilin_bounded hδ ⟨x.property.1.le, x.property.2.le⟩
  contMDiff := by
    intro x
    erw [contMDiffAt_section]
    apply (neckBilin_smooth hδ x).congr_of_eventuallyEq
    filter_upwards [] with y
    ext u v
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
    rfl

lemma slabChart_mfderiv_symm {x : E3} (hx : x ∈ slabChart.target) :
    mfderiv I3 I3 slabChart.symm x = (1 : E3 →L[ℝ] E3) := by
  have h := mfderivWithin_range_extChartAt_symm (I := I3) (x := slabChart.symm x)
  simp only [extChartAt_coe, extChartAt_coe_symm, chartAt_eq, I3,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.range_id, mfderivWithin_univ] at h
  rw [slabChart.right_inv hx] at h
  exact h

lemma neckMetric_matrix {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    {x : E3} (hx : x ∈ slabChart.target) :
    metricMatrix (neckMetric hδ) slabChart x = blockMatrix (Q δ (x 0)) := by
  ext i j
  simp only [metricMatrix, slabChart_mfderiv_symm hx]
  have hxval : (slabChart.symm x).val = x := slabChart.right_inv hx
  change metricBilin (blockMatrix (Q δ ((slabChart.symm x).val 0)))
    (basisVector i) (basisVector j) = _
  rw [hxval, metricBilin_apply]
  simp [basisVector, Pi.single_apply, Finset.sum_ite_irrel, mul_comm]

end

open Manifold Bundle Set Filter Cometric Neck Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma Q_mul_P {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    Q δ t * P δ t = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt (P_posDef hδ ht).det_pos))

lemma P_mul_Q {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    P δ t * Q δ t = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt (P_posDef hδ ht).det_pos))

lemma Q_transpose (δ t : ℝ) : (Q δ t)ᵀ = Q δ t := by
  rw [Q, Matrix.transpose_nonsing_inv,
    Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ t)]

lemma Q_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    HasDerivAt (Q δ) (deriv (Q δ) t) t :=
  ((Q_smoothAt hδ ht).differentiableAt (by simp)).hasDerivAt

lemma Q_deriv_transpose {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    (deriv (Q δ) t)ᵀ = deriv (Q δ) t := by
  have hQ := Q_hasDerivAt hδ ht
  ext i j
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp hQ j) i
  have heq : (fun r => Q δ r j i) = (fun r => Q δ r i j) := by
    funext r
    exact congrFun (congrFun (Q_transpose δ r) i) j
  rw [heq] at h
  exact h.unique (hasDerivAt_pi.mp (hasDerivAt_pi.mp hQ i) j)

lemma Q_deriv_jet {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Ioo 0 1) :
    deriv (Q δ) t = -Q δ t * P₁ δ t * Q δ t := by
  apply inverse_first_jet (P_hasDerivAt δ t) (Q_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩)
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact P_mul_Q hδ ⟨hr.1.le, hr.2.le⟩
  · exact Q_mul_P hδ ⟨ht.1.le, ht.2.le⟩

lemma P_hasDerivAt_Qjet {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (P δ) (-P δ t * deriv (Q δ) t * P δ t) t := by
  have h := inverse_first_jet (Q_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩)
    (P_hasDerivAt δ t)
    (show ∀ᶠ r in nhds t, Q δ r * P δ r = 1 from by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
      exact Q_mul_P hδ ⟨hr.1.le, hr.2.le⟩)
    (P_mul_Q hδ ⟨ht.1.le, ht.2.le⟩)
  rw [← h]
  exact P_hasDerivAt δ t

lemma Q_deriv_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    HasDerivAt (deriv (Q δ)) (deriv (deriv (Q δ)) t) t :=
  (((Q_smoothAt hδ ht).derivWithin (m := ∞) (by simp)).differentiableAt
    (by simp)).hasDerivAt

lemma slabChart_target : slabChart.target = {x : E3 | x 0 ∈ Ioo (0 : ℝ) 1} := by
  ext x
  constructor
  · intro hx
    have h := (slabChart.symm x).property
    rwa [show (slabChart.symm x).val = x from slabChart.right_inv hx] at h
  · intro hx
    exact slabChart.map_source (x := ⟨x, hx⟩) (by simp)

lemma neckMetric_germ {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    {x : E3} (hx : x ∈ slabChart.target) :
    metricMatrix (neckMetric hδ) slabChart =ᶠ[nhds x] fun y => blockMatrix (Q δ (y 0)) := by
  filter_upwards [slabChart.open_target.mem_nhds hx] with y hy
  exact neckMetric_matrix hδ hy

lemma neckMetric_connection {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    {x : E3} (hx : x ∈ slabChart.target) (u v : E3) :
    connectionTerm (neckMetric hδ) slabChart x u v =
      joinVector (gamma (P δ (x 0)) (deriv (Q δ) (x 0)) (splitVector u) (splitVector v)) := by
  have ht : x 0 ∈ Icc (0 : ℝ) 1 := by
    rw [slabChart_target] at hx
    exact ⟨hx.1.le, hx.2.le⟩
  exact connectionTerm_product _ _ (neckMetric_germ hδ hx)
    (Q_hasDerivAt hδ ht) (Q_mul_P hδ ht) (Q_deriv_transpose hδ ht) u v

lemma neckMetric_curvature {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    {x : E3} (hx : x ∈ slabChart.target) (u v w : E3) :
    curvatureTerm (neckMetric hδ) slabChart x u v w =
      joinVector (curvatureJet (P δ (x 0)) (deriv (Q δ) (x 0))
        (deriv (deriv (Q δ)) (x 0)) (splitVector u) (splitVector v) (splitVector w)) := by
  have ht : x 0 ∈ Ioo (0 : ℝ) 1 := by rwa [slabChart_target] at hx
  apply curvatureTerm_product _ _ (neckMetric_germ hδ hx)
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
    exact ⟨Q_hasDerivAt hδ hr', Q_mul_P hδ hr', Q_deriv_transpose hδ hr'⟩
  · exact P_hasDerivAt_Qjet hδ ht
  · exact Q_deriv_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩

def coordinates (γ : ℝ → Slab) : ℝ → E3 := fun s => (γ s).val

def torusVelocity (γ : ℝ → Slab) : ℝ → TVec :=
  fun s => ![deriv (coordinates γ) s 1, deriv (coordinates γ) s 2]

def momentum (δ : ℝ) (γ : ℝ → Slab) (s : ℝ) : TVec :=
  Q δ ((γ s).val 0) *ᵥ torusVelocity γ s

lemma coordinates_smooth {δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)} {γ : ℝ → Slab}
    {U : Set ℝ} (hγ : IsGeodesicOn (neckMetric hδ) γ U) :
    ContDiffOn ℝ ∞ (coordinates γ) U := by
  exact (slab_val_smooth.comp_contMDiffOn hγ.1).contDiffOn

lemma coordinates_smoothAt {δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)} {γ : ℝ → Slab}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (neckMetric hδ) γ U)
    {s : ℝ} (hs : s ∈ U) : ContDiffAt ℝ ∞ (coordinates γ) s :=
  (coordinates_smooth hγ).contDiffAt (hU.mem_nhds hs)

lemma coordinates_geodesic_equation {δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)} {γ : ℝ → Slab}
    {U : Set ℝ} (hγ : IsGeodesicOn (neckMetric hδ) γ U) {s : ℝ} (hs : s ∈ U) :
    deriv (deriv (coordinates γ)) s +
      joinVector (gamma (P δ ((γ s).val 0)) (deriv (Q δ) ((γ s).val 0))
        (splitVector (deriv (coordinates γ) s)) (splitVector (deriv (coordinates γ) s))) = 0 := by
  have h := hγ.2 slabChart (chart_mem_atlas E3 (γ s)) s hs (by simp)
  rw [alongDerivative, Function.comp_apply,
    neckMetric_connection hδ (slabChart.map_source (x := γ s) (by simp))] at h
  exact h

lemma momentum_hasDerivAt {δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)} {γ : ℝ → Slab}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (neckMetric hδ) γ U)
    {s : ℝ} (hs : s ∈ U) : HasDerivAt (momentum δ γ) 0 s := by
  have hx := ((coordinates_smoothAt hU hγ hs).differentiableAt (by simp)).hasDerivAt
  have hvel := (((coordinates_smoothAt hU hγ hs).derivWithin (m := ∞)
    (by simp)).differentiableAt (by simp)).hasDerivAt
  have hgeo := coordinates_geodesic_equation hγ hs
  have h2 : ![deriv (deriv (coordinates γ)) s 1, deriv (deriv (coordinates γ)) s 2] =
      -deriv (coordinates γ) s 0 •
        (P δ ((γ s).val 0) *ᵥ (deriv (Q δ) ((γ s).val 0) *ᵥ torusVelocity γ s)) := by
    ext i
    fin_cases i
    · have hi := congrFun hgeo 1
      dsimp [joinVector, gamma, splitVector] at hi
      dsimp [torusVelocity]
      nlinarith [hi]
    · have hi := congrFun hgeo 2
      dsimp [joinVector, gamma, splitVector] at hi
      dsimp [torusVelocity]
      nlinarith [hi]
  have hu : HasDerivAt (torusVelocity γ)
      (-deriv (coordinates γ) s 0 •
        (P δ ((γ s).val 0) *ᵥ (deriv (Q δ) ((γ s).val 0) *ᵥ torusVelocity γ s))) s := by
    rw [← h2]
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_pi.mp hvel 1
    · exact hasDerivAt_pi.mp hvel 2
  exact momentum_hasDerivAt_zero
    (t := fun r => (γ r).val 0) (v := fun r => deriv (coordinates γ) r 0)
    (u := torusVelocity γ)
    (Q_mul_P hδ ⟨(γ s).property.1.le, (γ s).property.2.le⟩)
    (Q_hasDerivAt hδ ⟨(γ s).property.1.le, (γ s).property.2.le⟩)
    (hasDerivAt_pi.mp hx 0) hu

end ThreeManifold.LocalNeck

namespace ThreeManifold.TorusNeck

section
open Set Filter Topology Manifold Bundle
open scoped ContDiff Matrix.Norms.Elementwise
open LocalNeck QuotientConstruction

abbrev Height := {t : ℝ // t ∈ Ioo (0 : ℝ) 1}
abbrev Neck (B₀ B₁ : ℝ) := Height × (AddCircle B₀ × AddCircle B₁)
abbrev Deck (B₀ B₁ : ℝ) := PUnit.{1} ×
  (Multiplicative (AddSubgroup.zmultiples B₀) × Multiplicative (AddSubgroup.zmultiples B₁))

instance : MulAction PUnit.{1} Height where
  smul _ t := t
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

lemma height_cover : IsQuotientCoveringMap (id : Height → Height) PUnit.{1} where
  __ := Homeomorph.refl Height |>.isQuotientMap
  continuous_const_smul _ := continuous_id
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro h
      exact ⟨PUnit.unit, h.symm⟩
    · rintro ⟨k, h⟩
      exact h.symm
  disjoint _ := ⟨univ, univ_mem, fun _ _ => Subsingleton.elim _ _⟩

instance torusProductAction (B₀ B₁ : ℝ) :
    MulAction (Multiplicative (AddSubgroup.zmultiples B₀) ×
      Multiplicative (AddSubgroup.zmultiples B₁)) (ℝ × ℝ) := productAction

instance neckProductAction (B₀ B₁ : ℝ) : MulAction (Deck B₀ B₁) (Height × (ℝ × ℝ)) :=
  productAction

def split : Slab ≃ₜ Height × (ℝ × ℝ) where
  toFun x := (⟨x.1 0, x.2⟩, x.1 1, x.1 2)
  invFun y := ⟨![y.1.1, y.2.1, y.2.2], y.1.2⟩
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv y := rfl
  continuous_toFun := by
    exact ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _ |>.prodMk
      (((continuous_apply 1).comp continuous_subtype_val).prodMk
        ((continuous_apply 2).comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_subtype_val.comp continuous_fst
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd

instance deckAction (B₀ B₁ : ℝ) : MulAction (Deck B₀ B₁) Slab :=
  split.toEquiv.mulAction (Deck B₀ B₁)

def projection (B₀ B₁ : ℝ) (x : Slab) : Neck B₀ B₁ :=
  (⟨x.1 0, x.2⟩, (x.1 1 : AddCircle B₀), (x.1 2 : AddCircle B₁))

lemma projection_cover (B₀ B₁ : ℝ) :
    IsQuotientCoveringMap (projection B₀ B₁) (Deck B₀ B₁) := by
  have h0 := (AddCircle.isAddQuotientCoveringMap_coe B₀).toMultiplicative _
  have h1 := (AddCircle.isAddQuotientCoveringMap_coe B₁).toMultiplicative _
  have ht := product_cover h0 h1
  have hn := product_cover height_cover ht
  exact cover_precomp hn split (fun _ _ => split.apply_symm_apply _)

lemma deck_val (B₀ B₁ : ℝ) (k : Deck B₀ B₁) (x : Slab) :
    (k • x).val = x.val + ![0, (Multiplicative.toAdd k.2.1).val,
      (Multiplicative.toAdd k.2.2).val] := by
  ext i
  fin_cases i
  · change x.val 0 = x.val 0 + 0
    ring
  · change (Multiplicative.toAdd k.2.1).val + x.val 1 =
      x.val 1 + (Multiplicative.toAdd k.2.1).val
    ring
  · change (Multiplicative.toAdd k.2.2).val + x.val 2 =
      x.val 2 + (Multiplicative.toAdd k.2.2).val
    ring

lemma deck_smooth (B₀ B₁ : ℝ) (k : Deck B₀ B₁) :
    ContMDiff I3 I3 ∞ (fun x : Slab => k • x) := by
  intro x
  rw [contMDiffAt_iff_target_of_mem_source (mem_chart_source E3 (k • x))]
  refine ⟨(projection_cover B₀ B₁).continuous_const_smul k |>.continuousAt, ?_⟩
  have hv : (fun y : Slab => slabChart (k • y)) = fun y => y.val +
      ![0, (Multiplicative.toAdd k.2.1).val, (Multiplicative.toAdd k.2.2).val] := by
    funext y
    exact deck_val B₀ B₁ k y
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_def, id_eq,
    chartAt_eq]
  rw [hv]
  exact (slab_val_smooth.contMDiffAt).add contMDiffAt_const

noncomputable def sectionMap (B₀ B₁ : ℝ) : Neck B₀ B₁ → Slab :=
  Function.surjInv (projection_cover B₀ B₁).surjective

lemma sectionMap_rightInverse (B₀ B₁ : ℝ) :
    Function.RightInverse (sectionMap B₀ B₁) (projection B₀ B₁) :=
  Function.rightInverse_surjInv (projection_cover B₀ B₁).surjective

instance neckCharts (B₀ B₁ : ℝ) : ChartedSpace E3 (Neck B₀ B₁) :=
  manifoldCharts (E := E3) (projection_cover B₀ B₁) (sectionMap_rightInverse B₀ B₁)

instance neckSmooth (B₀ B₁ : ℝ) : IsManifold I3 ∞ (Neck B₀ B₁) :=
  manifold_quotient_isManifold (projection_cover B₀ B₁) (sectionMap_rightInverse B₀ B₁)
    (deck_smooth B₀ B₁)

lemma projection_smooth (B₀ B₁ : ℝ) : ContMDiff I3 I3 ∞ (projection B₀ B₁) :=
  manifold_quotient_projection_smooth (projection_cover B₀ B₁)
    (sectionMap_rightInverse B₀ B₁) (deck_smooth B₀ B₁)

lemma neck_chart_eq (B₀ B₁ : ℝ) (q : Neck B₀ B₁) :
    chartAt E3 q = ((projection_cover B₀ B₁).isCoveringMap.isLocalHomeomorph.localInverseAt
      (sectionMap B₀ B₁ q)).trans slabChart := rfl

lemma chart_transition_germ (B₀ B₁ : ℝ) (a b : Neck B₀ B₁) {x : E3}
    (hx : x ∈ (chartAt E3 a).target)
    (hb : (chartAt E3 a).symm x ∈ (chartAt E3 b).source) :
    ∃ w : E3, w 0 = 0 ∧ ((chartAt E3 b) ∘ (chartAt E3 a).symm) =ᶠ[nhds x]
      (fun y => y + w) := by
  let hp := projection_cover B₀ B₁
  let l := hp.isCoveringMap.isLocalHomeomorph
  let db := l.localInverseAt (sectionMap B₀ B₁ b)
  have hx' : x ∈ slabChart.target := hx.1
  have hb' : projection B₀ B₁ (slabChart.symm x) ∈ db.source := by
    have h := hb.1
    simpa only [neck_chart_eq, OpenPartialHomeomorph.coe_trans_symm, Function.comp_def,
      IsLocalHomeomorph.localInverseAt_symm, OpenPartialHomeomorph.symm_target] using h
  obtain ⟨k, hk⟩ := cover_lift_eventuallyEq_action hp
    (fun k => (deck_smooth B₀ B₁ k).continuous) (sectionMap B₀ B₁ b) hb'
  refine ⟨![0, (Multiplicative.toAdd k.2.1).val, (Multiplicative.toAdd k.2.2).val], rfl, ?_⟩
  have hcomp := hk.comp_tendsto (slabChart.symm.continuousAt hx')
  have hnear : ∀ᶠ y in nhds x, y ∈ slabChart.target := slabChart.open_target.mem_nhds hx'
  filter_upwards [hcomp, hnear] with y hy hyt
  simp only [neck_chart_eq, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.coe_trans_symm, IsLocalHomeomorph.localInverseAt_symm,
    Function.comp_def]
  change slabChart (db (projection B₀ B₁ (slabChart.symm y))) = _
  change db (projection B₀ B₁ (slabChart.symm y)) = k • slabChart.symm y at hy
  rw [hy]
  change (k • slabChart.symm y).val = _
  rw [deck_val]
  have hr := slabChart.right_inv hyt
  change (slabChart.symm y).val = y at hr
  rw [hr]

lemma chart_transition_derivative (B₀ B₁ : ℝ) (a b : Neck B₀ B₁) {x : E3}
    (hx : x ∈ (chartAt E3 a).target)
    (hb : (chartAt E3 a).symm x ∈ (chartAt E3 b).source) :
    fderiv ℝ ((chartAt E3 b) ∘ (chartAt E3 a).symm) x = (1 : E3 →L[ℝ] E3) := by
  obtain ⟨w, _, hw⟩ := chart_transition_germ B₀ B₁ a b hx hb
  rw [hw.fderiv_eq]
  exact ((hasFDerivAt_id (𝕜 := ℝ) x).add_const w).fderiv

lemma neck_oriented (B₀ B₁ : ℝ) : OrientedAtlas (M := Neck B₀ B₁) := by
  intro c d hc hd x hx hd'
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨b, rfl⟩ := hd
  change 0 < LinearMap.det (fderiv ℝ ((chartAt E3 b) ∘ (chartAt E3 a).symm) x).toLinearMap
  rw [chart_transition_derivative B₀ B₁ a b hx hd']
  norm_num

lemma tangent_transition (B₀ B₁ : ℝ) (a b z : Neck B₀ B₁)
    (ha : z ∈ (chartAt E3 a).source) (hb : z ∈ (chartAt E3 b).source) :
    (tangentBundleCore I3 (Neck B₀ B₁)).coordChange (achart E3 a) (achart E3 b) z =
      (1 : E3 →L[ℝ] E3) := by
  rw [tangentBundleCore_coordChange_achart]
  simp only [extChartAt_coe, extChartAt_coe_symm, I3, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, range_id,
    fderivWithin_univ]
  apply chart_transition_derivative
  · exact (chartAt E3 a).map_source ha
  · rwa [(chartAt E3 a).left_inv ha]

lemma neck_symmL (B₀ B₁ : ℝ) (b z : Neck B₀ B₁)
    (hz : z ∈ (chartAt E3 b).source) :
    (trivializationAt E3 (TangentSpace I3) b).symmL ℝ z = (1 : E3 →L[ℝ] E3) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core hz]
  exact tangent_transition B₀ B₁ b z z hz (mem_chart_source E3 z)

lemma neck_linearMapAt (B₀ B₁ : ℝ) (b z : Neck B₀ B₁)
    (hz : z ∈ (chartAt E3 b).source) :
    (trivializationAt E3 (TangentSpace I3) b).continuousLinearMapAt ℝ z =
      (1 : E3 →L[ℝ] E3) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hz]
  exact tangent_transition B₀ B₁ z b z (mem_chart_source E3 z) hz

lemma height_smooth (B₀ B₁ : ℝ) :
    ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun q : Neck B₀ B₁ => q.1.val) := by
  intro q
  let hp := projection_cover B₀ B₁
  let l := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (sectionMap B₀ B₁ q)
  have hq : q ∈ l.source := by
    simpa only [sectionMap_rightInverse B₀ B₁ q] using
      hp.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
        (x := sectionMap B₀ B₁ q)
  have hl := local_lift_smoothAt hp (sectionMap_rightInverse B₀ B₁)
    (deck_smooth B₀ B₁) (sectionMap B₀ B₁ q) hq
  have hco : ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x : Slab => x.val 0) :=
    (contDiff_apply ℝ ℝ (0 : Fin 3)).contMDiff.comp slab_val_smooth
  apply ((hco (l q)).comp q hl).congr_of_eventuallyEq
  filter_upwards [l.open_source.mem_nhds hq] with r hr
  exact (congrArg (fun y : Neck B₀ B₁ => y.1.val)
    (hp.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hr)).symm

open Cometric Neck
lemma quotientBilin_smooth (B₀ B₁ : ℝ) {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    ContMDiff I3 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ) ∞
      (fun q : Neck B₀ B₁ => metricBilin (blockMatrix (Q δ q.1.val))) := by
  intro q
  have ht : q.1.val ∈ Icc (0 : ℝ) 1 := ⟨q.1.property.1.le, q.1.property.2.le⟩
  have hf : ContDiffAt ℝ ∞ (fun r => metricBilin (blockMatrix (Q δ r))) q.1.val :=
    metricBilin_smooth.contDiffAt.comp q.1.val
      (blockMatrix_smooth.contDiffAt.comp q.1.val (Q_smoothAt hδ ht))
  have hfM : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ) ∞
      (fun r => metricBilin (blockMatrix (Q δ r))) q.1.val := hf.contMDiffAt
  exact hfM.comp (f := fun y : Neck B₀ B₁ => y.1.val) q (height_smooth B₀ B₁ q)

def quotientMetric (B₀ B₁ : ℝ) {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    SmoothMetric (Neck B₀ B₁) where
  inner q := metricBilin (blockMatrix (Q δ q.1.val))
  symm q u v := neckBilin_symm hδ ⟨q.1.property.1.le, q.1.property.2.le⟩ u v
  pos q u hu := neckBilin_pos hδ ⟨q.1.property.1.le, q.1.property.2.le⟩ u hu
  isVonNBounded q := neckBilin_bounded hδ ⟨q.1.property.1.le, q.1.property.2.le⟩
  contMDiff := by
    let : ∀ point : Neck B₀ B₁, IsTopologicalAddGroup (TangentSpace I3 point →L[ℝ] ℝ) :=
      fun point => inferInstanceAs (IsTopologicalAddGroup (E3 →L[ℝ] ℝ))
    let : ∀ point : Neck B₀ B₁, ContinuousSMul ℝ (TangentSpace I3 point →L[ℝ] ℝ) :=
      fun point => inferInstanceAs (ContinuousSMul ℝ (E3 →L[ℝ] ℝ))
    intro q
    erw [contMDiffAt_section (F := E3 →L[ℝ] E3 →L[ℝ] ℝ)
      (E := fun point : Neck B₀ B₁ => TangentSpace I3 point →L[ℝ] TangentSpace I3 point →L[ℝ] ℝ) q]
    apply (quotientBilin_smooth B₀ B₁ hδ q).congr_of_eventuallyEq
    filter_upwards [(chartAt E3 q).open_source.mem_nhds (mem_chart_source E3 q)] with r hr
    ext u v
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      neck_symmL B₀ B₁ q r hr, Trivialization.linearMapAt_def_of_mem,
      TangentBundle.trivializationAt_baseSet, hr]
    rfl

lemma chart_symm_height (B₀ B₁ : ℝ) (q : Neck B₀ B₁) {x : E3}
    (hx : x ∈ (chartAt E3 q).target) :
    ((chartAt E3 q).symm x).1.val = x 0 := by
  have hx' : x ∈ slabChart.target := hx.1
  have hr := slabChart.right_inv hx'
  simp only [neck_chart_eq, OpenPartialHomeomorph.coe_trans_symm,
    IsLocalHomeomorph.localInverseAt_symm, Function.comp_def]
  change (slabChart.symm x).val 0 = x 0
  exact congrFun hr 0

lemma chart_symm_mfderiv (B₀ B₁ : ℝ) (q : Neck B₀ B₁) {x : E3}
    (hx : x ∈ (chartAt E3 q).target) :
    mfderiv I3 I3 (chartAt E3 q).symm x = (1 : E3 →L[ℝ] E3) := by
  have hs := (chartAt E3 q).map_target hx
  have h := TangentBundle.symmL_trivializationAt (I := I3) hs
  simp only [extChartAt_coe, extChartAt_coe_symm, I3,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, range_id, mfderivWithin_univ] at h
  rw [(chartAt E3 q).right_inv hx] at h
  rw [← h]
  exact neck_symmL B₀ B₁ q _ hs

lemma quotientMetric_matrix (B₀ B₁ : ℝ) {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (q : Neck B₀ B₁) {x : E3} (hx : x ∈ (chartAt E3 q).target) :
    metricMatrix (quotientMetric B₀ B₁ hδ) (chartAt E3 q) x = blockMatrix (Q δ (x 0)) := by
  ext i j
  simp only [metricMatrix, chart_symm_mfderiv B₀ B₁ q hx]
  change metricBilin (blockMatrix (Q δ (((chartAt E3 q).symm x).1.val)))
    (basisVector i) (basisVector j) = _
  rw [chart_symm_height B₀ B₁ q hx, metricBilin_apply]
  simp [basisVector, Pi.single_apply, Finset.sum_ite_irrel, mul_comm]

lemma quotientMetric_germ (B₀ B₁ : ℝ) {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (q : Neck B₀ B₁) {x : E3} (hx : x ∈ (chartAt E3 q).target) :
    metricMatrix (quotientMetric B₀ B₁ hδ) (chartAt E3 q) =ᶠ[nhds x]
      (fun y => blockMatrix (Q δ (y 0))) := by
  filter_upwards [(chartAt E3 q).open_target.mem_nhds hx] with y hy
  exact quotientMetric_matrix B₀ B₁ hδ q hy

end

open Set Filter Manifold Bundle Neck Cometric LocalNeck Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma chart_target_height (B₀ B₁ : ℝ) (q : Neck B₀ B₁) {x : E3}
    (hx : x ∈ (chartAt E3 q).target) : x 0 ∈ Ioo (0 : ℝ) 1 := by
  rw [← chart_symm_height B₀ B₁ q hx]
  exact ((chartAt E3 q).symm x).1.property

lemma quotientMetric_connection (B₀ B₁ : ℝ) {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (q : Neck B₀ B₁) {x : E3} (hx : x ∈ (chartAt E3 q).target) (u v : E3) :
    connectionTerm (quotientMetric B₀ B₁ hδ) (chartAt E3 q) x u v =
      joinVector (gamma (P δ (x 0)) (deriv (Q δ) (x 0)) (splitVector u) (splitVector v)) := by
  have ht := chart_target_height B₀ B₁ q hx
  exact connectionTerm_product _ _ (quotientMetric_germ B₀ B₁ hδ q hx)
    (Q_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩) (Q_mul_P hδ ⟨ht.1.le, ht.2.le⟩)
    (Q_deriv_transpose hδ ⟨ht.1.le, ht.2.le⟩) u v

lemma quotientMetric_curvature (B₀ B₁ : ℝ) {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (q : Neck B₀ B₁) {x : E3} (hx : x ∈ (chartAt E3 q).target) (u v w : E3) :
    curvatureTerm (quotientMetric B₀ B₁ hδ) (chartAt E3 q) x u v w =
      joinVector (curvatureJet (P δ (x 0)) (deriv (Q δ) (x 0))
        (deriv (deriv (Q δ)) (x 0)) (splitVector u) (splitVector v) (splitVector w)) := by
  have ht := chart_target_height B₀ B₁ q hx
  apply curvatureTerm_product _ _ (quotientMetric_germ B₀ B₁ hδ q hx)
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
    exact ⟨Q_hasDerivAt hδ hr', Q_mul_P hδ hr', Q_deriv_transpose hδ hr'⟩
  · exact P_hasDerivAt_Qjet hδ ht
  · exact Q_deriv_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩

lemma chart_mfderiv (B₀ B₁ : ℝ) (q z : Neck B₀ B₁)
    (hz : z ∈ (chartAt E3 q).source) :
    mfderiv I3 I3 (chartAt E3 q) z = (1 : E3 →L[ℝ] E3) := by
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (I := I3) hz
  simp only [extChartAt_coe, I3, modelWithCornersSelf_coe, Function.id_comp] at h
  rw [← h]
  exact neck_linearMapAt B₀ B₁ q z hz

lemma chart_height (B₀ B₁ : ℝ) (q z : Neck B₀ B₁)
    (hz : z ∈ (chartAt E3 q).source) : (chartAt E3 q z) 0 = z.1.val := by
  have h := chart_symm_height B₀ B₁ q ((chartAt E3 q).map_source hz)
  rw [(chartAt E3 q).left_inv hz] at h
  exact h.symm

def velocity {B₀ B₁ : ℝ} (γ : ℝ → Neck B₀ B₁) (s : ℝ) : E3 :=
  mfderiv 𝓘(ℝ, ℝ) I3 γ s 1

lemma velocity_eq_chart_deriv {B₀ B₁ : ℝ} {γ : ℝ → Neck B₀ B₁}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U)
    {s : ℝ} (hs : s ∈ U) (q : Neck B₀ B₁) (hq : γ s ∈ (chartAt E3 q).source) :
    velocity γ s = deriv ((chartAt E3 q) ∘ γ) s := by
  have hγs := (hγ.contMDiffAt (hU.mem_nhds hs)).mdifferentiableAt (by simp)
  have hqg : MDifferentiableAt I3 I3 (chartAt E3 q) (γ s) :=
    ((contMDiffOn_chart (I := I3) (n := ∞)).contMDiffAt ((chartAt E3 q).open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have h := mfderiv_comp s hqg hγs
  rw [chart_mfderiv B₀ B₁ q (γ s) hq] at h
  have hv := congrArg (fun L => L 1) h.symm
  change mfderiv 𝓘(ℝ, ℝ) I3 γ s 1 =
    mfderiv 𝓘(ℝ, ℝ) I3 ((chartAt E3 q) ∘ γ) s 1 at hv
  rw [mfderiv_eq_fderiv] at hv
  exact hv

lemma velocity_germ_chart {B₀ B₁ : ℝ} {γ : ℝ → Neck B₀ B₁}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U)
    {s : ℝ} (hs : s ∈ U) (q : Neck B₀ B₁) (hq : γ s ∈ (chartAt E3 q).source) :
    velocity γ =ᶠ[nhds s] deriv ((chartAt E3 q) ∘ γ) := by
  have hcts := (hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt
  filter_upwards [hU.mem_nhds hs,
    hcts.preimage_mem_nhds ((chartAt E3 q).open_source.mem_nhds hq)] with r hr hqr
  exact velocity_eq_chart_deriv hU hγ hr q hqr

lemma coord_smoothAt {B₀ B₁ : ℝ} {γ : ℝ → Neck B₀ B₁}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U)
    {s : ℝ} (hs : s ∈ U) (q : Neck B₀ B₁) (hq : γ s ∈ (chartAt E3 q).source) :
    ContDiffAt ℝ ∞ ((chartAt E3 q) ∘ γ) s := by
  exact (((contMDiffOn_chart (I := I3) (n := ∞)).contMDiffAt
    ((chartAt E3 q).open_source.mem_nhds hq)).comp s
    (hγ.contMDiffAt (hU.mem_nhds hs))).contDiffAt

lemma velocity_smoothAt {B₀ B₁ : ℝ} {γ : ℝ → Neck B₀ B₁}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U)
    {s : ℝ} (hs : s ∈ U) : ContDiffAt ℝ ∞ (velocity γ) s := by
  exact ((coord_smoothAt hU hγ hs (γ s) (mem_chart_source E3 (γ s))).derivWithin
    (m := ∞) (by simp)).congr_of_eventuallyEq
    (velocity_germ_chart hU hγ hs (γ s) (mem_chart_source E3 (γ s)))

lemma height_hasDerivAt {B₀ B₁ : ℝ} {γ : ℝ → Neck B₀ B₁}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U)
    {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (fun r => (γ r).1.val) (velocity γ s 0) s := by
  let q := γ s
  have hq := mem_chart_source E3 q
  rw [velocity_eq_chart_deriv hU hγ hs q hq]
  apply (hasDerivAt_pi.mp ((coord_smoothAt hU hγ hs q hq).differentiableAt
    (by simp)).hasDerivAt 0).congr_of_eventuallyEq
  have hcts := (hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt
  filter_upwards [hcts.preimage_mem_nhds ((chartAt E3 q).open_source.mem_nhds hq)] with r hr
  exact (chart_height B₀ B₁ q (γ r) hr).symm

lemma velocity_geodesic_equation {B₀ B₁ δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)}
    {γ : ℝ → Neck B₀ B₁} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn (quotientMetric B₀ B₁ hδ) γ U) {s : ℝ} (hs : s ∈ U) :
    deriv (velocity γ) s + joinVector
      (gamma (P δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
        (splitVector (velocity γ s)) (splitVector (velocity γ s))) = 0 := by
  let q := γ s
  have hq := mem_chart_source E3 q
  have h := hγ.2 (chartAt E3 q) (chart_mem_atlas E3 q) s hs hq
  rw [alongDerivative, Function.comp_apply,
    quotientMetric_connection B₀ B₁ hδ q ((chartAt E3 q).map_source hq),
    chart_height B₀ B₁ q (γ s) hq] at h
  rw [(velocity_germ_chart hU hγ.1 hs q hq).deriv_eq,
    velocity_eq_chart_deriv hU hγ.1 hs q hq]
  exact h

def fieldComponents {B₀ B₁ : ℝ} (γ : ℝ → Neck B₀ B₁)
    (J : ∀ s, TangentSpace I3 (γ s)) : ℝ → E3 := fun s => J s

lemma fieldCoordinates_eq {B₀ B₁ : ℝ} (γ : ℝ → Neck B₀ B₁)
    (J : ∀ s, TangentSpace I3 (γ s)) (q : Neck B₀ B₁) {s : ℝ}
    (hq : γ s ∈ (chartAt E3 q).source) : fieldCoordinates γ J (chartAt E3 q) s = J s := by
  rw [fieldCoordinates, chart_mfderiv B₀ B₁ q (γ s) hq]
  rfl

lemma fieldCoordinates_germ {B₀ B₁ : ℝ} {γ : ℝ → Neck B₀ B₁}
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ} (hγ : ContinuousAt γ s)
    (q : Neck B₀ B₁) (hq : γ s ∈ (chartAt E3 q).source) :
    fieldCoordinates γ J (chartAt E3 q) =ᶠ[nhds s] fieldComponents γ J := by
  filter_upwards [hγ.preimage_mem_nhds ((chartAt E3 q).open_source.mem_nhds hq)] with r hr
  exact fieldCoordinates_eq γ J q hr

lemma alongDerivative_eq {B₀ B₁ δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)}
    {γ : ℝ → Neck B₀ B₁} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U) (J : ∀ s, TangentSpace I3 (γ s))
    {s : ℝ} (hs : s ∈ U) (q : Neck B₀ B₁) (hq : γ s ∈ (chartAt E3 q).source) :
    alongDerivative (quotientMetric B₀ B₁ hδ) (chartAt E3 q)
      ((chartAt E3 q) ∘ γ) (fieldCoordinates γ J (chartAt E3 q)) s =
    deriv (fieldComponents γ J) s + joinVector
      (gamma (P δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
        (splitVector (velocity γ s)) (splitVector (J s))) := by
  rw [alongDerivative, Function.comp_apply,
    quotientMetric_connection B₀ B₁ hδ q ((chartAt E3 q).map_source hq),
    chart_height B₀ B₁ q (γ s) hq, fieldCoordinates_eq γ J q hq,
    ← velocity_eq_chart_deriv hU hγ hs q hq,
    (fieldCoordinates_germ J (hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt q hq).deriv_eq]

lemma split_add (u v : E3) : splitVector (u + v) = splitVector u + splitVector v := by
  apply Prod.ext
  · rfl
  · ext i; fin_cases i <;> rfl

def coordinateIndexDensity {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (γ : ℝ → M) (J : ∀ s, TangentSpace I3 (γ s)) (s : ℝ) : ℝ :=
  let x := c ∘ γ
  let w := fieldCoordinates γ J c
  let d := alongDerivative g c x w s
  metricBilin (metricMatrix g c (x s)) d d -
    metricBilin (metricMatrix g c (x s)) (w s)
      (curvatureTerm g c (x s) (w s) (deriv x s) (deriv x s))

lemma coordinateIndexDensity_eq {B₀ B₁ δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)}
    {γ : ℝ → Neck B₀ B₁} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U) (J : ∀ s, TangentSpace I3 (γ s))
    {s : ℝ} (hs : s ∈ U) (q : Neck B₀ B₁) (hq : γ s ∈ (chartAt E3 q).source) :
    coordinateIndexDensity (quotientMetric B₀ B₁ hδ) (chartAt E3 q) γ J s =
      let P := P δ ((γ s).1.val)
      let Q := Q δ ((γ s).1.val)
      let A := deriv (Cometric.Q δ) ((γ s).1.val)
      let B := deriv (deriv (Cometric.Q δ)) ((γ s).1.val)
      let T := splitVector (velocity γ s)
      let V := splitVector (J s)
      let Vdot := splitVector (deriv (fieldComponents γ J) s)
      metric Q (Vdot + gamma P A T V) (Vdot + gamma P A T V) -
        metric Q V (curvatureJet P A B V T T) := by
  dsimp only [coordinateIndexDensity]
  rw [alongDerivative_eq hU hγ J hs q hq]
  simp only [Function.comp_apply]
  rw [quotientMetric_matrix B₀ B₁ hδ q ((chartAt E3 q).map_source hq),
    quotientMetric_curvature B₀ B₁ hδ q ((chartAt E3 q).map_source hq),
    fieldCoordinates_eq γ J q hq, ← velocity_eq_chart_deriv hU hγ hs q hq]
  simp only [chart_height B₀ B₁ q (γ s) hq, metricBilin_block, split_add, split_join]
  congr 1
  exact (metricBilin_block _ (J s) _).trans (by rw [split_join])

lemma Q_second_transpose {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (deriv (deriv (Q δ)) t)ᵀ = deriv (deriv (Q δ)) t := by
  have hd := Q_deriv_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩
  ext i j
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd j) i
  have heq : (fun r => deriv (Q δ) r j i) =ᶠ[nhds t]
      (fun r => deriv (Q δ) r i j) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact congrFun (congrFun (Q_deriv_transpose hδ ⟨hr.1.le, hr.2.le⟩) i) j
  exact (h.congr_of_eventuallyEq heq.symm).unique
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j)

lemma actual_index_density_identity {B₀ B₁ δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)}
    {γ : ℝ → Neck B₀ B₁} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U) (J : ∀ s, TangentSpace I3 (γ s))
    {s : ℝ} (hs : s ∈ U) (q : Neck B₀ B₁) (hq : γ s ∈ (chartAt E3 q).source) :
    coordinateIndexDensity (quotientMetric B₀ B₁ hδ) (chartAt E3 q) γ J s =
      coordinateEnergyDensity (Q δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
        (deriv (deriv (Q δ)) ((γ s).1.val)) (splitVector (velocity γ s))
          (splitVector (J s)) (splitVector (deriv (fieldComponents γ J) s)) -
      boundaryJet (P δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
        (deriv (deriv (Q δ)) ((γ s).1.val)) (splitVector (velocity γ s))
          (splitVector (J s)) (splitVector (deriv (fieldComponents γ J) s)) := by
  rw [coordinateIndexDensity_eq hU hγ J hs q hq]
  have ht := (γ s).1.property
  exact index_density_identity (Q_mul_P hδ ⟨ht.1.le, ht.2.le⟩) (Q_transpose δ _)
    (Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ _))
    (Q_deriv_transpose hδ ⟨ht.1.le, ht.2.le⟩) (Q_second_transpose hδ ht) _ _ _

lemma splitVector_hasDerivAt {f : ℝ → E3} {f' : E3} {s : ℝ}
    (hf : HasDerivAt f f' s) :
    HasDerivAt (fun r => splitVector (f r)) (splitVector f') s := by
  apply (hasDerivAt_pi.mp hf 0).prodMk
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp hf 1
  · exact hasDerivAt_pi.mp hf 2

lemma split_neg (u : E3) : splitVector (-u) = -splitVector u := by
  apply Prod.ext
  · rfl
  · ext i; fin_cases i <;> rfl

lemma velocity_hasDerivAt {B₀ B₁ δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)}
    {γ : ℝ → Neck B₀ B₁} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn (quotientMetric B₀ B₁ hδ) γ U) {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (fun r => splitVector (velocity γ r))
      (-gamma (P δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
        (splitVector (velocity γ s)) (splitVector (velocity γ s))) s := by
  have h := splitVector_hasDerivAt
    ((velocity_smoothAt hU hγ.1 hs).differentiableAt (by simp)).hasDerivAt
  have hg := eq_neg_of_add_eq_zero_left (velocity_geodesic_equation hU hγ hs)
  rwa [hg, split_neg, split_join] at h

lemma actual_boundary_hasDerivAt {B₀ B₁ δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)}
    {γ : ℝ → Neck B₀ B₁} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn (quotientMetric B₀ B₁ hδ) γ U)
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ} (hs : s ∈ U)
    (hJ : DifferentiableAt ℝ (fieldComponents γ J) s) :
    HasDerivAt (fun r => boundaryTerm (deriv (Q δ) ((γ r).1.val))
      (splitVector (velocity γ r)) (splitVector (J r)))
      (boundaryJet (P δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
        (deriv (deriv (Q δ)) ((γ s).1.val)) (splitVector (velocity γ s))
          (splitVector (J s)) (splitVector (deriv (fieldComponents γ J) s))) s := by
  have ht := (γ s).1.property
  have hvel := velocity_hasDerivAt hU hγ hs
  have hfield := splitVector_hasDerivAt hJ.hasDerivAt
  have hv : HasDerivAt (fun r => velocity γ r 0)
      ((1 / 2 : ℝ) * pairing (deriv (Q δ) ((γ s).1.val))
        (splitVector (velocity γ s)).2 (splitVector (velocity γ s)).2) s := by
    have hp := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => velocity γ r 0)
      (-(gamma (P δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
        (splitVector (velocity γ s)) (splitVector (velocity γ s))).1) s at hp
    simpa only [gamma, neg_mul, neg_neg] using hp
  have hu : HasDerivAt (fun r => (splitVector (velocity γ r)).2)
      (-velocity γ s 0 • (P δ ((γ s).1.val) *ᵥ
        (deriv (Q δ) ((γ s).1.val) *ᵥ (splitVector (velocity γ s)).2))) s := by
    have hp := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => (splitVector (velocity γ r)).2)
      (-(gamma (P δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
        (splitVector (velocity γ s)) (splitVector (velocity γ s))).2) s at hp
    apply hp.congr_deriv
    ext i
    fin_cases i <;> simp [gamma, splitVector] <;> ring
  exact boundaryTerm_hasDerivAt
    (Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ _))
    (Q_deriv_transpose hδ ⟨ht.1.le, ht.2.le⟩) (Q_second_transpose hδ ht)
    (Q_deriv_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩) (height_hasDerivAt hU hγ.1 hs)
    hv hu ((ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hfield)
      ((ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hfield)

lemma Q_second_jet {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (Q δ)) t =
      (2 : ℝ) • (Q δ t * P₁ δ t * Q δ t * P₁ δ t * Q δ t) - Q δ t * P₂ δ t * Q δ t := by
  have hQ := Q_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩
  have h := matrix_mul_hasDerivAt
    (matrix_mul_hasDerivAt hQ.neg (P₁_hasDerivAt δ t)) hQ
  have heg : deriv (Q δ) =ᶠ[nhds t] (fun r => -Q δ r * P₁ δ r * Q δ r) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact Q_deriv_jet hδ hr
  have hid := (Q_deriv_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩).unique
    (h.congr_of_eventuallyEq heg)
  rw [hid, Q_deriv_jet hδ ht]
  simp only [Pi.neg_apply, neg_mul, mul_neg, neg_neg, add_mul, ← Matrix.mul_assoc]
  module

lemma splitVector_smooth : ContDiff ℝ ∞ splitVector := by
  apply (contDiff_apply ℝ ℝ 0).prodMk
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 1
  · exact contDiff_apply ℝ ℝ 2

lemma actual_index_integral {B₀ B₁ δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)}
    {γ : ℝ → Neck B₀ B₁} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn (quotientMetric B₀ B₁ hδ) γ U)
    (J : ∀ s, TangentSpace I3 (γ s))
    (hJ : ContDiffOn ℝ ∞ (fieldComponents γ J) U)
    {a b : ℝ} (hab : uIcc a b ⊆ U) :
    (∫ s in a..b, coordinateIndexDensity (quotientMetric B₀ B₁ hδ)
      (chartAt E3 (γ s)) γ J s) =
    (∫ s in a..b, coordinateEnergyDensity (Q δ ((γ s).1.val))
      (deriv (Q δ) ((γ s).1.val)) (deriv (deriv (Q δ)) ((γ s).1.val))
        (splitVector (velocity γ s)) (splitVector (J s))
          (splitVector (deriv (fieldComponents γ J) s))) -
    (boundaryTerm (deriv (Q δ) ((γ b).1.val)) (splitVector (velocity γ b)) (splitVector (J b)) -
      boundaryTerm (deriv (Q δ) ((γ a).1.val)) (splitVector (velocity γ a)) (splitVector (J a))) := by
  let t := fun s => (γ s).1.val
  let T := fun s => splitVector (velocity γ s)
  let V := fun s => splitVector (J s)
  let D := fun s => splitVector (deriv (fieldComponents γ J) s)
  have ht : ∀ s ∈ uIcc a b, ContinuousAt t s :=
    fun s hs => (height_hasDerivAt hU hγ.1 (hab hs)).continuousAt
  have hP : ContinuousOn (P δ ∘ t) (uIcc a b) := by
    intro s hs
    exact ((P_smooth δ).continuous.continuousAt.comp (ht s hs)).continuousWithinAt
  have hQ : ContinuousOn (Q δ ∘ t) (uIcc a b) := by
    intro s hs
    have hr := (γ s).1.property
    have hc : ContinuousAt (Q δ) (t s) := (Q_smoothAt hδ ⟨hr.1.le, hr.2.le⟩).continuousAt
    exact (hc.comp (ht s hs)).continuousWithinAt
  have hA : ContinuousOn (deriv (Q δ) ∘ t) (uIcc a b) := by
    intro s hs
    have hr := (γ s).1.property
    have hc : ContinuousAt (deriv (Q δ)) (t s) :=
      ((Q_smoothAt hδ ⟨hr.1.le, hr.2.le⟩).derivWithin (m := ∞) (by simp)).continuousAt
    exact (hc.comp (ht s hs)).continuousWithinAt
  have hB : ContinuousOn (deriv (deriv (Q δ)) ∘ t) (uIcc a b) := by
    intro s hs
    have hr := (γ s).1.property
    have hc : ContinuousAt (deriv (deriv (Q δ))) (t s) :=
      (((Q_smoothAt hδ ⟨hr.1.le, hr.2.le⟩).derivWithin (m := ∞) (by simp)).derivWithin
        (m := ∞) (by simp)).continuousAt
    exact (hc.comp (ht s hs)).continuousWithinAt
  have hT : ContinuousOn T (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp
      (velocity_smoothAt hU hγ.1 (hab hs)).continuousAt).continuousWithinAt
  have hV : ContinuousOn V (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp
      (hJ.contDiffAt (hU.mem_nhds (hab hs))).continuousAt).continuousWithinAt
  have hD : ContinuousOn D (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp
      ((hJ.contDiffAt (hU.mem_nhds (hab hs))).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  let E := fun s => coordinateEnergyDensity (Q δ (t s)) (deriv (Q δ) (t s))
    (deriv (deriv (Q δ)) (t s)) (T s) (V s) (D s)
  let B := fun s => boundaryJet (P δ (t s)) (deriv (Q δ) (t s))
    (deriv (deriv (Q δ)) (t s)) (T s) (V s) (D s)
  have he : ContinuousOn E (uIcc a b) := continuousOn_energy hQ hA hB hT hV hD
  have hb : ContinuousOn B (uIcc a b) := continuousOn_boundaryJet hP hA hB hT hV hD
  have hderiv : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r => boundaryTerm (deriv (Q δ) (t r)) (T r) (V r)) (B s) s := by
    intro s hs
    exact actual_boundary_hasDerivAt hU hγ J (hab hs)
      ((hJ.contDiffAt (hU.mem_nhds (hab hs))).differentiableAt (by simp))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hb.intervalIntegrable
  calc
    _ = ∫ s in a..b, E s - B s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact actual_index_density_identity hU hγ.1 J (hab hs) (γ s) (mem_chart_source E3 (γ s))
    _ = (∫ s in a..b, E s) - ∫ s in a..b, B s :=
      intervalIntegral.integral_sub he.intervalIntegrable hb.intervalIntegrable
    _ = _ := by rw [hFTC]

def momentum {B₀ B₁ : ℝ} (δ : ℝ) (γ : ℝ → Neck B₀ B₁) (s : ℝ) : TVec :=
  Q δ ((γ s).1.val) *ᵥ (splitVector (velocity γ s)).2

lemma momentum_hasDerivAt {B₀ B₁ δ : ℝ} {hδ : δ ∈ Icc 0 (1 / 2)}
    {γ : ℝ → Neck B₀ B₁} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn (quotientMetric B₀ B₁ hδ) γ U) {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (momentum δ γ) 0 s := by
  have ht := (γ s).1.property
  have hvel := velocity_hasDerivAt hU hγ hs
  have hu : HasDerivAt (fun r => (splitVector (velocity γ r)).2)
      (-velocity γ s 0 • (P δ ((γ s).1.val) *ᵥ
        (deriv (Q δ) ((γ s).1.val) *ᵥ (splitVector (velocity γ s)).2))) s := by
    have hp := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => (splitVector (velocity γ r)).2)
      (-(gamma (P δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
        (splitVector (velocity γ s)) (splitVector (velocity γ s))).2) s at hp
    apply hp.congr_deriv
    ext i
    fin_cases i <;> simp [gamma, splitVector] <;> ring
  exact momentum_hasDerivAt_zero (v := fun r => velocity γ r 0) (Q_mul_P hδ ⟨ht.1.le, ht.2.le⟩)
    (Q_hasDerivAt hδ ⟨ht.1.le, ht.2.le⟩) (height_hasDerivAt hU hγ.1 hs) hu

lemma velocity_eq_momentum {B₀ B₁ δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (γ : ℝ → Neck B₀ B₁) (s : ℝ) :
    splitVector (velocity γ s) = (velocity γ s 0, P δ ((γ s).1.val) *ᵥ momentum δ γ s) := by
  have ht := (γ s).1.property
  have hp := mul_eq_one_comm.mp (Q_mul_P hδ ⟨ht.1.le, ht.2.le⟩)
  apply Prod.ext
  · rfl
  · simp only [momentum, Matrix.mulVec_mulVec, hp, Matrix.one_mulVec]

lemma P₁_transpose (δ t : ℝ) : (P₁ δ t)ᵀ = P₁ δ t := by
  have hP := P_hasDerivAt δ t
  ext i j
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp hP j) i
  have heq : (fun r => P δ r j i) = (fun r => P δ r i j) := by
    funext r
    exact congrFun (congrFun (Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ r)) i) j
  rw [heq] at h
  exact h.unique (hasDerivAt_pi.mp (hasDerivAt_pi.mp hP i) j)

lemma actual_energy_cometric {B₀ B₁ δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (γ : ℝ → Neck B₀ B₁) (J : ∀ s, TangentSpace I3 (γ s)) (s : ℝ) :
    coordinateEnergyDensity (Q δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
      (deriv (deriv (Q δ)) ((γ s).1.val)) (splitVector (velocity γ s))
        (splitVector (J s)) (splitVector (deriv (fieldComponents γ J) s)) =
    (deriv (fieldComponents γ J) s 0) ^ 2 +
      pairing (Q δ ((γ s).1.val))
        ((splitVector (deriv (fieldComponents γ J) s)).2 -
          J s 0 • (P₁ δ ((γ s).1.val) *ᵥ momentum δ γ s))
        ((splitVector (deriv (fieldComponents γ J) s)).2 -
          J s 0 • (P₁ δ ((γ s).1.val) *ᵥ momentum δ γ s)) -
      (1 / 2 : ℝ) * pairing (P₂ δ ((γ s).1.val)) (momentum δ γ s) (momentum δ γ s) *
        (J s 0) ^ 2 := by
  have ht := (γ s).1.property
  rw [Q_deriv_jet hδ ht, Q_second_jet hδ ht, velocity_eq_momentum hδ]
  exact energy_cometric_identity (Q_mul_P hδ ⟨ht.1.le, ht.2.le⟩)
    (Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ _)) (Q_transpose δ _)
    (P₁_transpose δ _) (momentum δ γ s) (velocity γ s 0) _ _

lemma pairing_eq_qform (A : TMat) (p : TVec) : pairing A p p = qform A p := rfl

theorem uniform_actual_energy_nonneg : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀, ∀ B₀ B₁ : ℝ, ∀ γ : ℝ → Neck B₀ B₁,
      ∀ J : ∀ s, TangentSpace I3 (γ s), ∀ s : ℝ,
        0 ≤ coordinateEnergyDensity (Q δ ((γ s).1.val)) (deriv (Q δ) ((γ s).1.val))
          (deriv (deriv (Q δ)) ((γ s).1.val)) (splitVector (velocity γ s))
            (splitVector (J s)) (splitVector (deriv (fieldComponents γ J) s)) := by
  obtain ⟨δ₀, C, hd0, hdhalf, hC, hb⟩ := uniform_original_bounds
  refine ⟨δ₀, hd0, hdhalf, ?_⟩
  intro δ hδ B₀ B₁ γ J s
  have hδ' : δ ∈ Icc (0 : ℝ) (1 / 2) := ⟨hδ.1.le, hδ.2.trans hdhalf⟩
  have ht := (γ s).1.property
  rw [actual_energy_cometric hδ']
  have hconc := (hb δ hδ _ ⟨ht.1.le, ht.2.le⟩ (momentum δ γ s)).2.2.2.1
  rw [P₂_deriv] at hconc
  change 0 ≤ pairing (-P₂ δ ((γ s).1.val)) (momentum δ γ s) (momentum δ γ s) at hconc
  rw [pairing_matrix_neg] at hconc
  have hpos := (Q_elliptic hδ' ⟨ht.1.le, ht.2.le⟩
    ((splitVector (deriv (fieldComponents γ J) s)).2 -
      J s 0 • (P₁ δ ((γ s).1.val) *ᵥ momentum δ γ s))).1
  change _ ≤ pairing _ _ _ at hpos
  have hn := sqnorm_nonneg ((splitVector (deriv (fieldComponents γ J) s)).2 -
      J s 0 • (P₁ δ ((γ s).1.val) *ᵥ momentum δ γ s))
  have hh : 0 ≤ (deriv (fieldComponents γ J) s 0) ^ 2 := sq_nonneg _
  have hw : 0 ≤ (J s 0) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg (neg_nonneg.mpr (neg_nonneg.mp hconc)) hw]

end ThreeManifold.TorusNeck

end

end OAI
