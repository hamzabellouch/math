import Mathlib
import OAI.Algebra.FrobeniusObstruction.TensorKernels

namespace OAI

noncomputable section
open scoped BigOperators TensorProduct

namespace BoundaryOnly.FormalObstruction.BlockCohomology
open SquareZero MixedForms
variable {k A ι : Type*} [Field k] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]
variable (pd : ι → Derivation k A A) (q : A)

                                                                       
                                                                                
structure Contraction where
  j : H pd q →ₗ[k] Forms (k := k) (A := A) (ι := ι)
  p : Forms (k := k) (A := A) (ι := ι) →ₗ[k] H pd q
  h : Module.End k (Forms (k := k) (A := A) (ι := ι))
  cycle_j : ∀ x, delta pd q (j x) = 0
  p_boundary : ∀ x, p (delta pd q x) = 0
  p_j : ∀ x, p (j x) = x
  p_cycle : ∀ z : Cycles (delta pd q), p z = classMap _ (delta_sq pd q) z
  j_parity : ∀ x, j (P pd q x) = parity (j x)
  p_parity : ∀ x, p (parity x) = P pd q (p x)
  h_parity : ∀ x, h (parity x) = -parity (h x)
  homotopy : ∀ x, x - j (p x) = delta pd q (h x) + h (delta pd q x)

 theorem contraction_exists (htwo : (2 : k) ≠ 0) : Nonempty (Contraction pd q) := by
  obtain ⟨j,p,h,hj,hp,hpj,hpc,hjP,hpP,hhP,hh⟩ := parity_cohomology_contraction
    htwo (delta pd q) parity.toLinearMap (delta_sq pd q) parity_sq (delta_parity pd q)
  exact ⟨⟨j,p,h,hj,hp,hpj,hpc,hjP,hpP,hhP,hh⟩⟩

def contraction (htwo : (2 : k) ≠ 0) : Contraction pd q :=
  Classical.choice (contraction_exists pd q htwo)

namespace Contraction
variable {pd q} (c : Contraction pd q)

 theorem class_j (x : H pd q) :
    classMap _ (delta_sq pd q) ⟨c.j x, c.cycle_j x⟩ = x :=
  (c.p_cycle ⟨c.j x, c.cycle_j x⟩).symm.trans (c.p_j x)

 theorem project_odd (f : Module.End k (Forms (k := k) (A := A) (ι := ι)))
    (hf : ∀ x, delta pd q (f x) = -f (delta pd q x)) (x : H pd q) :
    c.p (f (c.j x)) = oddInduced _ (delta_sq pd q) f hf x := by
  conv_rhs => rw [← c.class_j x, oddInduced_class, ← c.p_cycle]
  rfl

 theorem project_even (f : Module.End k (Forms (k := k) (A := A) (ι := ι)))
    (hf : ∀ x, delta pd q (f x) = f (delta pd q x)) (x : H pd q) :
    c.p (f (c.j x)) = evenInduced _ (delta_sq pd q) f hf x := by
  conv_rhs => rw [← c.class_j x, evenInduced_class, ← c.p_cycle]
  rfl

 theorem project_d (hc : ∀ i j a, pd i (pd j a) = pd j (pd i a)) (x : H pd q) :
    c.p (d pd (c.j x)) = D pd q hc x :=
  c.project_odd (d pd) (delta_d pd q hc) x

 theorem project_coefficient (s : A) (x : H pd q) :
    c.p (coefficient s (c.j x)) = S pd q s x :=
  c.project_even (coefficient s) (delta_coefficient pd q s) x

end Contraction
end BoundaryOnly.FormalObstruction.BlockCohomology

namespace BoundaryOnly.FormalObstruction.SignedTensor
variable {k ι : Type*} [Field k] [Fintype ι] [LinearOrder ι]
variable {V W : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

theorem differential_map (P D : EndFamily (k := k) V) (Q E : EndFamily (k := k) W)
    (f : ∀ i, V i →ₗ[k] W i)
    (hP : ∀ i, (f i).comp (P i) = (Q i).comp (f i))
    (hD : ∀ i, (f i).comp (D i) = (E i).comp (f i)) :
    (PiTensorProduct.map f).comp (differential V P D) =
      (differential W Q E).comp (PiTensorProduct.map f) := by
  apply PiTensorProduct.ext
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    differential, LinearMap.sum_apply, PiTensorProduct.map_tprod, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext a
  by_cases ha : a < i
  · simp only [dSlot, ite_eq_left ha]
    exact LinearMap.congr_fun (hP a) (v a)
  · by_cases he : a = i
    · simp only [dSlot, ite_eq_right ha, ite_eq_left he]
      exact LinearMap.congr_fun (hD a) (v a)
    · simp only [dSlot, ite_eq_right ha, ite_eq_right he, Module.End.one_apply]

end BoundaryOnly.FormalObstruction.SignedTensor

namespace BoundaryOnly.FormalObstruction.BlockTensor
open MixedForms SquareZero SignedTensor
variable {k t : Type*} [Field k] [Fintype t] [LinearOrder t]
variable (A K : t → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)]
  [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
abbrev V (i : t) := Forms (k := k) (A := A i) (ι := K i)
variable {A K}
variable (pd : ∀ i, K i → Derivation k (A i) (A i)) (q : ∀ i, A i)
abbrev H (i : t) := BlockCohomology.H (pd i) (q i)
def P : EndFamily (k := k) (V (k := k) A K) := fun _ => parity.toLinearMap
local notation "PV" => (P (k := k) (A := A) (K := K))
def D : EndFamily (k := k) (V (k := k) A K) := fun i => d (pd i)
def delta : EndFamily (k := k) (V (k := k) A K) := fun i => MixedForms.delta (pd i) (q i)
def S (s : ∀ i, A i) : EndFamily (k := k) (V (k := k) A K) :=
  fun i => BlockCohomology.coefficient (s i)
def HP : EndFamily (k := k) (H pd q) := fun i => BlockCohomology.P (pd i) (q i)
def HD (hc : ∀ a i j x, pd a i (pd a j x) = pd a j (pd a i x)) :
    EndFamily (k := k) (H pd q) := fun i => BlockCohomology.D (pd i) (q i) (hc i)
def HS (s : ∀ i, A i) : EndFamily (k := k) (H pd q) :=
  fun i => BlockCohomology.S (pd i) (q i) (s i)
variable (c : ∀ i, BlockCohomology.Contraction (pd i) (q i))
def j : (⨂[k] i, H pd q i) →ₗ[k] (⨂[k] i, V (k := k) A K i) :=
  PiTensorProduct.map (fun i => (c i).j)
def p : (⨂[k] i, V (k := k) A K i) →ₗ[k] (⨂[k] i, H pd q i) :=
  PiTensorProduct.map (fun i => (c i).p)

theorem projection_boundary (x : ⨂[k] i, V (k := k) A K i) :
    p pd q c (differential (V (k := k) A K) PV (delta pd q) x) = 0 := by
  exact LinearMap.congr_fun (projection_boundaries PV (delta pd q)
    (fun i => (c i).p) (fun i => by apply LinearMap.ext; intro z; exact (c i).p_boundary z)) x

theorem representatives_cycle (x : ⨂[k] i, H pd q i) :
    differential (V (k := k) A K) PV (delta pd q) (j pd q c x) = 0 := by
  exact LinearMap.congr_fun (representatives_cycles PV (delta pd q)
    (fun i => (c i).j) (fun i => by apply LinearMap.ext; intro z; exact (c i).cycle_j z)) x

theorem cycle_decomposition (z : ⨂[k] i, V (k := k) A K i)
    (hz : differential (V (k := k) A K) PV (delta pd q) z = 0) :
    ∃ y, z - j pd q c (p pd q c z) = differential (V (k := k) A K) PV (delta pd q) y := by
  apply tensor_cycle_decomposition PV (delta pd q)
    (fun i => (c i).j) (fun i => (c i).p) (fun i => (c i).h) _ _ _ _ _ _ _ z hz
  · intro i; apply LinearMap.ext; intro x; exact parity_sq x
  · intro i; apply LinearMap.ext; intro x; exact BlockCohomology.delta_parity (pd i) (q i) x
  · intro i; apply LinearMap.ext; intro x; exact (c i).cycle_j x
  · intro i; apply LinearMap.ext; intro x; exact (c i).p_boundary x
  · intro i; apply LinearMap.ext; intro x
    change parity ((c i).j ((c i).p x)) = (c i).j ((c i).p (parity x))
    rw [(c i).p_parity, (c i).j_parity]
  · intro i; apply LinearMap.ext; intro x
    change parity ((c i).h x) = -(c i).h (parity x)
    rw [(c i).h_parity, neg_neg]
  · intro i; apply LinearMap.ext; intro x
    exact ((c i).homotopy x).symm

omit [Fintype t] [LinearOrder t] in
theorem project_parity (i : t) :
    (c i).p.comp ((PV i).comp (c i).j) = HP pd q i := by
  apply LinearMap.ext; intro x
  change (c i).p (parity ((c i).j x)) = BlockCohomology.P (pd i) (q i) x
  rw [(c i).p_parity, (c i).p_j]

theorem project_D (hc : ∀ a i j x, pd a i (pd a j x) = pd a j (pd a i x)) :
    (p pd q c).comp ((differential (V (k := k) A K) PV (D pd)).comp (j pd q c)) =
      differential (H pd q) (HP pd q) (HD pd q hc) := by
  apply project_differential
  · intro i; apply LinearMap.ext; intro x; exact (c i).p_j x
  · exact project_parity pd q c
  · intro i; apply LinearMap.ext; intro x; exact (c i).project_d (hc i) x

omit [Fintype t] in
theorem project_S (s : ∀ i, A i) (I : Finset t) :
    (p pd q c).comp ((tensorAction (V (k := k) A K) (S s) I).comp (j pd q c)) =
      tensorAction (H pd q) (HS pd q s) I := by
  apply project_tensor_map
  intro i
  by_cases hi : i ∈ I
  · apply LinearMap.ext; intro x
    simpa only [tensorAction, ite_eq_left hi, LinearMap.comp_apply, S, HS]
      using (c i).project_coefficient (s i) x
  · apply LinearMap.ext; intro x
    simpa only [tensorAction, ite_eq_right hi, LinearMap.comp_apply, LinearMap.id_apply]
      using (c i).p_j x

end BoundaryOnly.FormalObstruction.BlockTensor

namespace BoundaryOnly.FormalObstruction.SignedTensor
variable {k t : Type*} [Field k] [Fintype t] [LinearOrder t]
variable (V : t → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

theorem differential_anticomm (P D E : EndFamily (k := k) V)
    (hP : ∀ i, P i * P i = 1)
    (hD : ∀ i, D i * P i = -(P i * D i))
    (hE : ∀ i, P i * E i = -(E i * P i))
    (hDE : ∀ i, D i * E i + E i * D i = 0) :
    differential V P D * differential V P E +
      differential V P E * differential V P D = 0 := by
  have hh : homotopy V P (fun _ => 1) E = differential V P E := by
    unfold homotopy differential
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  have h := tensor_homotopy P D (fun _ => 1) E hP hD
    (fun i => by simp only [mul_one, one_mul])
    (fun i => by simp only [mul_one, one_mul]) hE
    (fun i => by rw [sub_self]; exact hDE i)
  rw [hh] at h
  have hi : PiTensorProduct.map (fun i : t => (1 : Module.End k (V i))) = 1 :=
    PiTensorProduct.map_id
  rwa [hi, sub_self] at h

end BoundaryOnly.FormalObstruction.SignedTensor

namespace BoundaryOnly.FormalObstruction.BlockTensor
open MixedForms SquareZero SignedTensor
variable {k t : Type*} [Field k] [Fintype t] [LinearOrder t]
variable {A K : t → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)]
  [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
variable (pd : ∀ i, K i → Derivation k (A i) (A i)) (q : ∀ i, A i)
local notation "PV" => (P (k := k) (A := A) (K := K))

theorem D_delta_anticomm (hc : ∀ a i j x, pd a i (pd a j x) = pd a j (pd a i x))
    (x : ⨂[k] i, V (k := k) A K i) :
    differential (V (k := k) A K) PV (D pd)
      (differential (V (k := k) A K) PV (delta pd q) x) =
    -differential (V (k := k) A K) PV (delta pd q)
      (differential (V (k := k) A K) PV (D pd) x) := by
  have h := differential_anticomm (V (k := k) A K) PV (D pd) (delta pd q)
    (fun i => by apply LinearMap.ext; intro y; exact parity_sq y)
    (fun i => by apply LinearMap.ext; intro y; exact d_parity (pd i) y)
    (fun i => by
      apply LinearMap.ext; intro y
      change parity (MixedForms.delta (pd i) (q i) y) =
        -MixedForms.delta (pd i) (q i) (parity y)
      rw [BlockCohomology.delta_parity, neg_neg])
    (fun i => by
      apply LinearMap.ext; intro y
      change d (pd i) (MixedForms.delta (pd i) (q i) y) +
        MixedForms.delta (pd i) (q i) (d (pd i) y) = 0
      exact d_delta (pd i) (hc i) (q i) y)
  exact eq_neg_of_add_eq_zero_left (LinearMap.congr_fun h x)

theorem S_delta_comm (s : ∀ i, A i) (I : Finset t)
    (x : ⨂[k] i, V (k := k) A K i) :
    tensorAction (V (k := k) A K) (S s) I
      (differential (V (k := k) A K) PV (delta pd q) x) =
    differential (V (k := k) A K) PV (delta pd q)
      (tensorAction (V (k := k) A K) (S s) I x) := by
  apply LinearMap.congr_fun (differential_map PV (delta pd q) PV (delta pd q)
    (fun i => if i ∈ I then S s i else LinearMap.id) ?_ ?_) x
  · intro i
    by_cases hi : i ∈ I
    · simp only [ite_eq_left hi]
      apply LinearMap.ext; intro y
      change coeff (s i) * parity y = parity (coeff (s i) * y)
      rw [map_mul, parity_coeff]
    · simp only [ite_eq_right hi, LinearMap.id_comp, LinearMap.comp_id]
  · intro i
    by_cases hi : i ∈ I
    · simp only [ite_eq_left hi]
      apply LinearMap.ext; intro y
      exact (BlockCohomology.delta_coefficient (pd i) (q i) (s i) y).symm
    · simp only [ite_eq_right hi, LinearMap.id_comp, LinearMap.comp_id]

end BoundaryOnly.FormalObstruction.BlockTensor

namespace BoundaryOnly.FormalObstruction.BlockTensor
open MixedForms SquareZero SignedTensor
variable {k t : Type*} [Field k] [Fintype t] [LinearOrder t]
variable {A K : t → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)]
  [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
variable (pd : ∀ i, K i → Derivation k (A i) (A i)) (q : ∀ i, A i)
local notation "PV" => (P (k := k) (A := A) (K := K))
local notation "Ω" => (V (k := k) A K)
local notation "δt" => (differential Ω PV (delta pd q))
local notation "Dt" => (differential Ω PV (D pd))

theorem project_D_cycle
    (hc : ∀ a i j x, pd a i (pd a j x) = pd a j (pd a i x))
    (c : ∀ i, BlockCohomology.Contraction (pd i) (q i))
    (z : ⨂[k] i, Ω i) (hz : δt z = 0) :
    differential (H pd q) (HP pd q) (HD pd q hc) (p pd q c z) = p pd q c (Dt z) := by
  refine CycleTransfer.operator (H := ⨂[k] i, H pd q i) δt (j pd q c) (p pd q c)
    (projection_boundary pd q c) (cycle_decomposition pd q c) Dt (-Dt)
    (differential (H pd q) (HP pd q) (HD pd q hc)) ?_ ?_ z hz
  · intro x
    simpa only [LinearMap.neg_apply, map_neg] using D_delta_anticomm pd q hc x
  · intro x
    exact (LinearMap.congr_fun (project_D pd q c hc) x).symm

theorem pairing_project_D
    (hc : ∀ a i j x, pd a i (pd a j x) = pd a j (pd a i x))
    (c : ∀ i, BlockCohomology.Contraction (pd i) (q i))
    (Φ : (⨂[k] i, Ω i) →ₗ[k] k)
    (hΦδ : ∀ x, Φ (δt x) = 0) (hΦD : ∀ x, Φ (Dt x) = 0)
    (x : ⨂[k] i, H pd q i) :
    Φ (j pd q c (differential (H pd q) (HP pd q) (HD pd q hc) x)) = 0 := by
  refine CycleTransfer.pairing_operator (H := ⨂[k] i, H pd q i) δt (j pd q c) (p pd q c)
    (cycle_decomposition pd q c) Dt (-Dt)
    (differential (H pd q) (HP pd q) (HD pd q hc)) ?_ ?_ ?_ Φ hΦδ hΦD x
  · intro z
    change _ = -(Dt (δt z))
    rw [D_delta_anticomm pd q hc z, neg_neg]
  · exact representatives_cycle pd q c
  · intro z
    exact (LinearMap.congr_fun (project_D pd q c hc) z).symm

theorem project_S_cycle
    (c : ∀ i, BlockCohomology.Contraction (pd i) (q i))
    (s : ∀ i, A i) (I : Finset t)
    (z : ⨂[k] i, Ω i) (hz : δt z = 0) :
    tensorAction (H pd q) (HS pd q s) I (p pd q c z) =
      p pd q c (tensorAction Ω (S s) I z) := by
  refine CycleTransfer.operator (H := ⨂[k] i, H pd q i) δt (j pd q c) (p pd q c)
    (projection_boundary pd q c) (cycle_decomposition pd q c)
    (tensorAction Ω (S s) I) (tensorAction Ω (S s) I)
    (tensorAction (H pd q) (HS pd q s) I) ?_ ?_ z hz
  · exact S_delta_comm pd q s I
  · intro x
    exact (LinearMap.congr_fun (project_S pd q c s I) x).symm

                                                                               
                                                                             
theorem selected_classes (htwo : (2 : k) ≠ 0)
    (hc : ∀ a i j x, pd a i (pd a j x) = pd a j (pd a i x))
    (s : ∀ i, A i) (active : Finset t) (hcard : 5 ≤ active.card)
    (c : ∀ i, BlockCohomology.Contraction (pd i) (q i))
    (Φ : (⨂[k] i, Ω i) →ₗ[k] k)
    (hΦδ : ∀ x, Φ (δt x) = 0) (hΦD : ∀ x, Φ (Dt x) = 0)
    (z : ⨂[k] i, Ω i) (hz : δt z = 0) (hDz : Dt z = 0) (hΦz : Φ z ≠ 0)
    (htriple : ∀ I : Finset t, I ⊆ active → I.card = 3 →
      ∃ y, tensorAction Ω (S s) I z = δt y) :
    ∃ (J : Finset t) (m : ∀ i, H pd q i),
      J ⊆ active ∧ 3 ≤ J.card ∧
      (∀ i ∈ J, HS pd q s i (m i) = 0 ∧
        HS pd q s i (HD pd q hc i (m i)) = 0) ∧
      Φ (j pd q c (PiTensorProduct.tprod k m)) ≠ 0 := by
  let φ := Φ.comp (j pd q c)
  have hHD : differential (H pd q) (HP pd q) (HD pd q hc) (p pd q c z) = 0 := by
    rw [project_D_cycle pd q hc c z hz, hDz, map_zero]
  have hφD (x : ⨂[k] i, H pd q i) :
      φ (differential (H pd q) (HP pd q) (HD pd q hc) x) = 0 :=
    pairing_project_D pd q hc c Φ hΦδ hΦD x
  have hφz : φ (p pd q c z) ≠ 0 := by
    change Φ (j pd q c (p pd q c z)) ≠ 0
    rw [CycleTransfer.pairing (H := ⨂[k] i, H pd q i) δt (j pd q c) (p pd q c) (cycle_decomposition pd q c) Φ hΦδ z hz]
    exact hΦz
  have hSz (I : Finset t) (hi : I ⊆ active) (hI : I.card = 3) :
      tensorAction (H pd q) (HS pd q s) I (p pd q c z) = 0 := by
    rw [project_S_cycle pd q c s I z hz]
    obtain ⟨y,hy⟩ := htriple I hi hI
    rw [hy, projection_boundary]
  choose r h hrD hrP hhP hDh hNr using
    (fun i => BlockCohomology.retraction (pd i) (q i) (hc i) htwo (s i))
  apply select_special_fiber_tensor (HS pd q s) (HP pd q) (HD pd q hc) r h
    active hcard _ _ _ _ _ _ _ φ hφD (p pd q c z) hHD hφz hSz
  · intro i; apply LinearMap.ext; intro x; exact BlockCohomology.P_sq (pd i) (q i) x
  · intro i; apply LinearMap.ext; intro x; exact BlockCohomology.D_P (pd i) (q i) (hc i) x
  · intro i; apply LinearMap.ext; intro x; exact hrD i x
  · intro i; apply LinearMap.ext; intro x; exact hrP i x
  · intro i; apply LinearMap.ext; intro x; exact hhP i x
  · intro i; apply LinearMap.ext; intro x; exact (hDh i x).symm
  · intro i _ x hx; exact hNr i x hx

                                                                           
                                                                    
theorem selected_cycles (htwo : (2 : k) ≠ 0)
    (hc : ∀ a i j x, pd a i (pd a j x) = pd a j (pd a i x))
    (s : ∀ i, A i) (active : Finset t) (hcard : 5 ≤ active.card)
    (Φ : (⨂[k] i, Ω i) →ₗ[k] k)
    (hΦδ : ∀ x, Φ (δt x) = 0) (hΦD : ∀ x, Φ (Dt x) = 0)
    (z : ⨂[k] i, Ω i) (hz : δt z = 0) (hDz : Dt z = 0) (hΦz : Φ z ≠ 0)
    (htriple : ∀ I : Finset t, I ⊆ active → I.card = 3 →
      ∃ y, tensorAction Ω (S s) I z = δt y) :
    ∃ (J : Finset t) (x : ∀ i, Ω i),
      J ⊆ active ∧ 3 ≤ J.card ∧ (∀ i, delta pd q i (x i) = 0) ∧
      (∀ i ∈ J, ∃ y : Ω i, delta pd q i y = -MixedForms.delta (pd i) (s i) (x i)) ∧
      Φ (PiTensorProduct.tprod k x) ≠ 0 := by
  let c := fun i => BlockCohomology.contraction (pd i) (q i) htwo
  obtain ⟨J,m,hJ,hcardJ,hm,hpair⟩ := selected_classes pd q htwo hc s active hcard c
    Φ hΦδ hΦD z hz hDz hΦz htriple
  refine ⟨J,fun i => (c i).j (m i),hJ,hcardJ,?_,?_,?_⟩
  · intro i; exact (c i).cycle_j (m i)
  · intro i hi
    apply BlockCohomology.correction (pd i) (q i) (hc i) (s i)
      ⟨(c i).j (m i), (c i).cycle_j (m i)⟩
    · rw [(c i).class_j]; exact (hm i hi).1
    · rw [(c i).class_j]; exact (hm i hi).2
  · simpa only [j, PiTensorProduct.map_tprod] using hpair

end BoundaryOnly.FormalObstruction.BlockTensor

end

end OAI
