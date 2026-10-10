import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairData.Data

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

def coordinateChunk0 : Array (Fin 909) := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64]

def coordinateChunk1 : Array (Fin 909) := #[65, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 89, 94, 95, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 110, 112, 113, 114, 115, 116, 119, 120, 122, 123, 124, 125, 126, 127, 128, 129, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 177]

def coordinateChunk2 : Array (Fin 909) := #[190, 191, 196, 197, 199, 201, 203, 204, 205, 207, 208, 209, 216, 217, 226, 228, 230, 231, 236, 237, 238, 239, 253, 256, 257, 259, 260, 262, 266, 267, 268, 271, 273, 275, 276, 277, 278, 279, 280, 281, 282, 284, 286, 287, 288, 289, 290, 291, 293, 299, 300, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318]

def coordinateChunk3 : Array (Fin 909) := #[319, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 352, 378, 379, 383, 392, 398, 399, 400, 425, 426, 428, 453, 460, 472, 489, 490, 492, 493, 494, 495, 498, 499, 500, 501, 502, 503, 505, 506, 507, 508, 517, 538, 539, 540, 541, 543, 545, 546, 640, 643, 702, 709, 721, 723, 726, 727, 728, 735, 736, 737, 738, 739, 745]

def coordinateChunk4 : Array (Fin 909) := #[751, 753, 760, 764, 783, 784, 794, 796, 798, 810, 811, 812, 818, 855, 870]

def coordinateMap (i : Fin 271) : Fin 909 :=
  ((#[coordinateChunk0, coordinateChunk1, coordinateChunk2, coordinateChunk3, coordinateChunk4])[i.val / 64]!)[i.val % 64]!

noncomputable def momentVector (H : CMatrix) : Fin 271 → ℝ :=
  PairSemantics.momentVector H ∘ coordinateMap

end MUB6.Certificate.PairSourceBridge

end OAI
