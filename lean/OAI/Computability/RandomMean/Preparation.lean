import OAI.Computability.RandomMean.Allocation

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Preparation
abbrev Seed := (Count×Count)×(W×RawControl.Acc)
abbrev Aux := (Count×Count)×Count×(W×RawControl.Acc)
noncomputable def inputLength : Code Digits Count := by
  let F := Map.device (TreeDevice.constant boolData Median.unitData ())
  refine ⟨fun d => d.bits.map (fun _ => ()),F.recode encode encode Digits.bits
    (fun d => d.bits.map (fun _ => ())) (fun _ => rfl) (fun _ => rfl),?_⟩
  obtain ⟨K,d,h⟩ := PolynomialCost.map (LinearCost.constant boolData Median.unitData ()).polynomial
  exact ⟨K,d,fun z => h z.bits⟩
noncomputable def logarithm : Code Digits Count :=
  inputLength ≫ₚ Counter.inc ≫ₚ Counter.inc ≫ₚ Counter.word ≫ₚ NaturalLog.ceil
noncomputable def exponent : Code Digits Count :=
  ((const (List.replicate 25000 ())) ⋏ₚ (logarithm ≫ₚ Counter.fixedPower 2)) ≫ₚ Counter.mul
noncomputable def root : Code Digits Seed := InputCode.parse ≫ₚ
  ((RootCode.exponent ⋏ₚ RootCode.samples) ⋏ₚ (InputCode.width ⋏ₚ (RootCode.env ⋏ₚ RootCode.state)))
noncomputable def seed : Code Digits (Count×Seed) := exponent ⋏ₚ root
noncomputable def inflate : Device encode encode
    (fun z : Count×Seed => (Fold.fold Allocation.double.eval [()] z.1,z.2)) :=
  pairMap Allocation.device (TreeDevice.identity encode)
noncomputable def assemble : Code (Count×Seed) (Count×Aux) :=
  (((snd ≫ₚ fst ≫ₚ fst) ⋏ₚ fst) ≫ₚ Counter.mul) ⋏ₚ ((snd ≫ₚ fst) ⋏ₚ fst ⋏ₚ (snd ≫ₚ snd))
noncomputable def value (d : Digits) : Count×Aux :=
  assemble (Fold.fold Allocation.double.eval [()] (exponent d),root d)
noncomputable def device : Device encode encode value :=
  @compose Digits (Count×Seed) (Count×Aux) encode encode encode seed.eval
    (fun z => assemble (Fold.fold Allocation.double.eval [()] z.1,z.2)) seed.device
    (@compose (Count×Seed) (Count×Seed) (Count×Aux) encode encode encode
      (fun z => (Fold.fold Allocation.double.eval [()] z.1,z.2)) assemble.eval inflate assemble.device)
 theorem logarithm_length (d : Digits) : (logarithm d).length=Nat.clog 2 (d.bits.length+2) := by
  change (NaturalLog.ceil (Counter.word (Counter.inc (Counter.inc (inputLength d))))).length=_
  rw [NaturalLog.ceil_exact _ (by rw [Counter.word_val]; simp only [Counter.inc_length]; positivity),Counter.word_val,Int.toNat_natCast]
  change Nat.clog 2 ((d.bits.map (fun _ => ())).length+1+1)=_
  simp only [List.length_map,Nat.add_assoc]
 theorem exponent_length (d : Digits) : (exponent d).length=25000*(Nat.clog 2 (d.bits.length+2))^2 := by
  simp only [exponent,comp_eval,pair_eval,Counter.mul_length,const_eval,List.length_replicate,Counter.fixedPower_length,logarithm_length]
 theorem iterations (d : Digits) : (value d).2.2.1=List.replicate (2^(exponent d).length) () := Allocation.exact _
 theorem bits_length (d : Digits) : (value d).1.length=(root d).1.1.length*2^(exponent d).length := by
  change (Counter.mul ((root d).1.1,Fold.fold Allocation.double.eval [()] (exponent d))).length=_
  rw [Counter.mul_length,Allocation.exact,List.length_replicate]
 theorem aux (d : Digits) : (value d).2=((root d).1,List.replicate (2^(exponent d).length) (), (root d).2) := by
  change ((root d).1,Fold.fold Allocation.double.eval [()] (exponent d),(root d).2)=_
  rw [Allocation.exact]
end Preparation
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified.Preparation
open BinaryData
 theorem seed_eval (d : Digits) : seed d=(exponent d,root d) := rfl
 theorem inflate_limit (z : Count×Seed) : inflate.limit z=Allocation.device.limit z.1+1+
    24*treeSize (encode (Fold.fold Allocation.double.eval [()] z.1))+24*treeSize (encode z.2)+50 := by
  rcases z with ⟨c,s⟩
  rw [inflate,pairMap_limit]
  change _+1+24*_+12*_+12*_+50=_
  simp only [id_eq]
  omega
 theorem device_limit (d : Digits) : device.limit d=
    seed.device.limit d+inflate.limit (seed d)+
      assemble.device.limit (Fold.fold Allocation.double.eval [()] (exponent d),root d)+4 := by
  simp only [device, compose_limit]
  simp only [seed_eval]
  omega
end MeanPayoff.TreeDevice.Certified.Preparation

end

section
namespace MeanPayoff.TreeDevice.Certified.Preparation
open BinaryData
 theorem exponent_poly : PolynomialCost exponent.device := exponent.polynomial
 theorem root_poly : PolynomialCost root.device := root.polynomial
 theorem seed_poly : PolynomialCost seed.device := PolynomialCost.fanout exponent_poly root_poly
 theorem assemble_poly : PolynomialCost assemble.device := assemble.polynomial
end MeanPayoff.TreeDevice.Certified.Preparation

end

section
namespace MeanPayoff.TreeDevice.Certified.Preparation
open BinaryData
noncomputable def resource (d : Digits) : ℕ := treeSize (encode d)+2^(exponent d).length
 theorem input_bound : PolyBound resource (fun d => treeSize (encode d)) :=
  (PolyBound.base resource).mono (fun _ => Nat.le_add_right _ _)
 theorem seed_cost : PolyBound resource seed.device.limit := by
  obtain ⟨K,e,h⟩ := seed_poly
  refine ⟨K,e,fun d => (h d).trans ?_⟩
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.le_add_right _ _) 1
 theorem seed_size_le (d : Digits) : treeSize (encode (seed d)) ≤ treeSize (encode d)+seed.device.limit d :=
  output_size seed.device d
 theorem seed_size : PolyBound resource (fun d => treeSize (encode (seed d))) :=
  (input_bound.add seed_cost).mono seed_size_le
 theorem exponent_size : PolyBound resource (fun d => treeSize (encode (exponent d))) := by
  apply seed_size.mono
  intro d
  have h := Size.fst (seed d)
  rw [seed_eval] at h
  exact h
 theorem exponent_size_length : PolyBound resource (fun d => (exponent d).length) :=
  exponent_size.mono (fun _ => Size.length _)
 theorem power_bound : PolyBound resource (fun d => 2^(exponent d).length) :=
  (PolyBound.base resource).mono (fun _ => Nat.le_add_left _ _)
 theorem allocation_init_cost : PolyBound resource (fun d => Allocation.init.device.limit (exponent d)) :=
  polynomial_limit Allocation.init.polynomial resource exponent exponent_size
 theorem allocation_fold_cost : PolyBound resource
    (fun d => (Fold.device Allocation.double.device).limit ([()],exponent d)) := by
  obtain ⟨K,e,hK⟩ := Allocation.fold_bound
  apply ((PolyBound.const resource K).mul
    (((power_bound.add exponent_size_length).add (PolyBound.const resource 1)).pow e)).mono
  intro d
  simpa only [List.length_cons,List.length_nil,Nat.zero_add,Nat.one_mul,Nat.add_comm] using hK [()] (exponent d)
 theorem allocation_cost : PolyBound resource (fun d => Allocation.device.limit (exponent d)) := by
  apply ((allocation_init_cost.add allocation_fold_cost).add (PolyBound.const resource 2)).mono
  intro d
  rfl
 theorem allocation_size : PolyBound resource
    (fun d => treeSize (encode (Fold.fold Allocation.double.eval [()] (exponent d)))) :=
  polynomial_output Allocation.device resource exponent exponent_size allocation_cost
 theorem root_size : PolyBound resource (fun d => treeSize (encode (root d))) := by
  apply seed_size.mono
  intro d
  have h := Size.snd (seed d)
  rw [seed_eval] at h
  exact h
 theorem inflate_cost : PolyBound resource (fun d => inflate.limit (seed d)) := by
  apply ((((allocation_cost.add (PolyBound.const resource 1)).add
    ((PolyBound.const resource 24).mul allocation_size)).add
    ((PolyBound.const resource 24).mul root_size)).add (PolyBound.const resource 50)).mono
  intro d
  rw [inflate_limit,seed_eval]
 theorem inflate_size : PolyBound resource
    (fun d => treeSize (encode (Fold.fold Allocation.double.eval [()] (exponent d),root d))) := by
  have h := polynomial_output inflate resource (fun d => seed d) seed_size inflate_cost
  simpa only [seed_eval] using h
 theorem assemble_cost : PolyBound resource
    (fun d => assemble.device.limit (Fold.fold Allocation.double.eval [()] (exponent d),root d)) :=
  @polynomial_limit Digits (Count×Seed) (Count×Aux) encode encode assemble.eval assemble.device
    assemble_poly resource (fun d => (Fold.fold Allocation.double.eval [()] (exponent d),root d)) inflate_size
 theorem cost_bound : PolyBound resource device.limit := by
  apply (((seed_cost.add inflate_cost).add assemble_cost).add (PolyBound.const resource 4)).mono
  intro d
  rw [device_limit]
 theorem output_size_le (d : Digits) : treeSize (encode (value d)) ≤ treeSize (encode d)+device.limit d :=
  output_size device d
 theorem output_bound : PolyBound resource (fun d => treeSize (encode (value d))) :=
  (input_bound.add cost_bound).mono output_size_le
end MeanPayoff.TreeDevice.Certified.Preparation

end

end OAI
