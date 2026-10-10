import Mathlib
import OAI.Algebra.FiniteTensor.SquarefreeParameters

namespace OAI

/-! Separated potentials, parameter selection and complementary deformed graphs. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped BigOperators
universe u
variable (K : Type*) [Field K] (p : ℕ) {n : ℕ}
  (σ : Fin (n+1) → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

 
def formalSigmaPotential (F : ∀ i,MvPowerSeries (σ i) K) :
    MvPowerSeries ((i : Fin (n+1)) × σ i) K :=
  ∑ i,MvPowerSeries.rename (Sigma.mk i) (F i)

 
def formalSigmaSelected (b : ∀ i,MvPowerSeries (σ i) K) (s : Finset (Fin (n+1))) :
    MvPowerSeries ((i : Fin (n+1)) × σ i) K :=
  ∏ i∈s,MvPowerSeries.rename (Sigma.mk i) (b i)

 
def formalSigmaDeformed (F b : ∀ i,MvPowerSeries (σ i) K) (q : Fin 3 ↪ Fin (n+1)) :
    MvPowerSeries ((i : Fin (n+1)) × σ i) (T K 3) :=
  MvPowerSeries.map (algebraMap K (T K 3)) (formalSigmaPotential K σ F) +
    ∑ i,MvPowerSeries.C (threeParameters (K:=K) q i) *
      MvPowerSeries.map (algebraMap K (T K 3)) (MvPowerSeries.rename (Sigma.mk i) (b i))

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped BigOperators
universe u
variable (K : Type*) [Field K] {n : ℕ} (σ : Fin (n+1) → Type u)
  [∀ i,Fintype (σ i)] (m : ℕ)

 

def formalActiveDeformed (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K) :
    MvPowerSeries ((i : Fin (n+1)) × σ i) (T K m) :=
  MvPowerSeries.map (algebraMap K (T K m)) (formalSigmaPotential K σ F) +
    ∑ j,MvPowerSeries.C (t K m j)*MvPowerSeries.map (algebraMap K (T K m))
      (MvPowerSeries.rename (Sigma.mk (active j)) (b j))

theorem augmentation_formalActiveDeformed (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K) :
    MvPowerSeries.map (augmentation K m) (formalActiveDeformed K σ m F active b)=
      formalSigmaPotential K σ F := by
  classical
  have hc : (augmentation K m).comp (algebraMap K (T K m))=RingHom.id K := by
    ext a
    exact (augmentationAlg K m).commutes a
  simp only [formalActiveDeformed,map_add,map_sum,map_mul,MvPowerSeries.map_C,
    MvPowerSeries.map_map,hc,augmentation_t,map_zero,zero_mul,Finset.sum_const_zero,
    add_zero,MvPowerSeries.map_id,RingHom.id_apply]

theorem sum_threeParameters_activeExtension
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K)
    (q : Fin 3 ↪ Fin (n+1)) :
    (∑ i,MvPowerSeries.C (threeParameters (K:=K) q i)*
      MvPowerSeries.map (algebraMap K (T K 3))
        (MvPowerSeries.rename (Sigma.mk i) (activeExtension (A:=fun i => MvPowerSeries (σ i) K) active b i)))=
    ∑ j,MvPowerSeries.C (threeParameters (K:=K) q (active j))*
      MvPowerSeries.map (algebraMap K (T K 3))
        (MvPowerSeries.rename (Sigma.mk (active j)) (b j)) := by
  classical
  let f : ∀ i,MvPowerSeries (σ i) K →+ MvPowerSeries ((i : Fin (n+1)) × σ i) (T K 3) :=
    fun i => {
      toFun := fun a => MvPowerSeries.C (threeParameters (K:=K) q i)*
        MvPowerSeries.map (algebraMap K (T K 3)) (MvPowerSeries.rename (Sigma.mk i) a)
      map_zero' := by simp only [map_zero,mul_zero]
      map_add' := fun a b => by simp only [map_add,mul_add] }
  exact sum_activeExtension (A:=fun i => MvPowerSeries (σ i) K) active b f

theorem selector_formalActiveDeformed (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K)
    (q : Fin 3 ↪ Fin (n+1)) :
    MvPowerSeries.map (parameterSelector K m active q).toRingHom
      (formalActiveDeformed K σ m F active b)=
      formalSigmaDeformed K σ F (activeExtension active b) q := by
  classical
  have hc : (parameterSelector K m active q).toRingHom.comp (algebraMap K (T K m))=
      algebraMap K (T K 3) := by
    ext a
    exact (parameterSelector K m active q).commutes a
  simp only [formalActiveDeformed,formalSigmaDeformed,map_add,map_sum,map_mul,
    MvPowerSeries.map_C,MvPowerSeries.map_map]
  erw [hc]
  simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,parameterSelector_t]
  congr 1
  exact (sum_threeParameters_activeExtension K σ m active b q).symm

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped BigOperators
universe u
variable (K : Type*) [Field K] {n : ℕ} (σ : Fin (n+1) → Type u)
  [∀ i,Fintype (σ i)] (m : ℕ)

theorem augmentation_selector_graph {υ τ : Type*}
    (active : Fin m ↪ Fin (n+1)) (q : Fin 3 ↪ Fin (n+1))
    (H : υ → MvPowerSeries τ (T K m)) (i : υ) :
    MvPowerSeries.map (augmentation K 3)
        (MvPowerSeries.map (parameterSelector K m active q).toRingHom (H i))=
      MvPowerSeries.map (augmentation K m) (H i) := by
  ext d
  simp only [MvPowerSeries.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
    augmentation_parameterSelector]

theorem central_graph_zero {d : ℕ} (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K)
    (H : ((i : Fin (n+1)) × σ i) → MvPowerSeries (Fin d) (T K m))
    (hH : MvPowerSeries.HasSubst H)
    (hL : MvPowerSeries.subst H (formalActiveDeformed K σ m F active b)=0) :
    MvPowerSeries.subst (fun i => MvPowerSeries.map (augmentation K m) (H i))
      (formalSigmaPotential K σ F)=0 := by
  have hh := congrArg (MvPowerSeries.map (augmentation K m)) hL
  rw [MvPowerSeries.map_subst hH,augmentation_formalActiveDeformed,map_zero] at hh
  exact hh

theorem selector_graph_zero {d : ℕ} (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K)
    (H : ((i : Fin (n+1)) × σ i) → MvPowerSeries (Fin d) (T K m))
    (hH : MvPowerSeries.HasSubst H)
    (hL : MvPowerSeries.subst H (formalActiveDeformed K σ m F active b)=0)
    (q : Fin 3 ↪ Fin (n+1)) :
    MvPowerSeries.subst (fun i => MvPowerSeries.map (parameterSelector K m active q).toRingHom (H i))
      (formalSigmaDeformed K σ F (activeExtension active b) q)=0 := by
  have hh := congrArg (MvPowerSeries.map (parameterSelector K m active q).toRingHom) hL
  rw [MvPowerSeries.map_subst hH,selector_formalActiveDeformed,map_zero] at hh
  exact hh

theorem selector_graph_triple {d : ℕ} (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K)
    (H : ((i : Fin (n+1)) × σ i) → MvPowerSeries (Fin d) (T K m))
    (hH : MvPowerSeries.HasSubst H)
    (htrip : ∀ i j k : Fin m,i≠j → i≠k → j≠k →
      MvPowerSeries.C (t K m i*t K m j*t K m k)∈Ideal.span
        (Set.range (fun x => MvPowerSeries.subst H
          (MvPowerSeries.pderiv x (formalActiveDeformed K σ m F active b)))))
    (q : Fin 3 ↪ Fin (n+1)) (hq : ∀ j,q j∈Set.range active) :
    MvPowerSeries.C (t K 3 0*t K 3 1*t K 3 2)∈Ideal.span
      (Set.range (fun x =>
        MvPowerSeries.subst (fun i => MvPowerSeries.map (parameterSelector K m active q).toRingHom (H i))
          (MvPowerSeries.pderiv x (formalSigmaDeformed K σ F (activeExtension active b) q)))) := by
  classical
  obtain ⟨r,hr⟩ := embedding_preimage active q hq
  have h01 : r 0≠r 1 := r.injective.ne (by decide)
  have h02 : r 0≠r 2 := r.injective.ne (by decide)
  have h12 : r 1≠r 2 := r.injective.ne (by decide)
  have ht : MvPowerSeries.subst H
      (MvPowerSeries.C (t K m (r 0)*t K m (r 1)*t K m (r 2)))∈Ideal.span
        (Set.range (fun x => MvPowerSeries.subst H
          (MvPowerSeries.pderiv x (formalActiveDeformed K σ m F active b)))) := by
    simpa only [MvPowerSeries.subst_C] using htrip (r 0) (r 1) (r 2) h01 h02 h12
  have hh := map_formal_gradient (parameterSelector K m active q).toRingHom H hH
    (formalActiveDeformed K σ m F active b)
    (MvPowerSeries.C (t K m (r 0)*t K m (r 1)*t K m (r 2))) ht
  rw [selector_formalActiveDeformed] at hh
  have hscalar : (parameterSelector K m active q).toRingHom
      (t K m (r 0)*t K m (r 1)*t K m (r 2))=t K 3 0*t K 3 1*t K 3 2 := by
    simp only [map_mul,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      parameterSelector_t,hr,threeParameters_selected]
  rw [MvPowerSeries.map_C,hscalar,MvPowerSeries.subst_C] at hh
  exact hh

theorem formalSigmaSelected_active_triple
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K)
    (i j k : Fin m) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    formalSigmaSelected K σ (activeExtension active b) {active i,active j,active k}=
      MvPowerSeries.rename (Sigma.mk (active i)) (b i)*
      MvPowerSeries.rename (Sigma.mk (active j)) (b j)*
      MvPowerSeries.rename (Sigma.mk (active k)) (b k) := by
  classical
  simp [formalSigmaSelected,active.injective.ne hij,active.injective.ne hik,
    active.injective.ne hjk,mul_assoc]

 

theorem active_right_triples {c : ℕ} (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K)
    (G : ((i : Fin (n+1)) × σ i) → MvPowerSeries (Fin c) K)
    (htrip : ∀ i j k : Fin m,i≠j → i≠k → j≠k →
      MvPowerSeries.subst G
        (MvPowerSeries.rename (Sigma.mk (active i)) (b i)*
          MvPowerSeries.rename (Sigma.mk (active j)) (b j)*
          MvPowerSeries.rename (Sigma.mk (active k)) (b k))∈Ideal.span
            (Set.range (fun x => MvPowerSeries.subst G
              (MvPowerSeries.pderiv x (formalSigmaPotential K σ F)))))
    (s : Finset (Fin (n+1))) (hs : ∀ i∈s,i∈Set.range active) (hc : s.card=3) :
    MvPowerSeries.subst G (formalSigmaSelected K σ (activeExtension active b) s)∈Ideal.span
      (Set.range (fun x => MvPowerSeries.subst G
        (MvPowerSeries.pderiv x (formalSigmaPotential K σ F)))) := by
  classical
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := Finset.card_eq_three.mp hc
  obtain ⟨i,rfl⟩ := hs x (by simp)
  obtain ⟨j,rfl⟩ := hs y (by simp)
  obtain ⟨k,rfl⟩ := hs z (by simp)
  have hij : i≠j := fun h => hxy (congrArg active h)
  have hik : i≠k := fun h => hxz (congrArg active h)
  have hjk : j≠k := fun h => hyz (congrArg active h)
  rw [formalSigmaSelected_active_triple K σ m active b i j k hij hik hjk]
  exact htrip i j k hij hik hjk

end
end PD4Tensor.TruncatedForms
end

end OAI
